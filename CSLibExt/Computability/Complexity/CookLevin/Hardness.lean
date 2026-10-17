/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.DenseSATInNP
public import CSLibExt.Computability.Complexity.EncodingConverters
public import CSLibExt.Computability.Complexity.CookLevin.Package

/-!
# Cook-Levin for dense CNF-SAT on the canonical classes

Every decision problem in formal-math's canonical `MetaMathlibExt.ComplexityTheory.NP`
polynomial-time many-one reduces (`Cslib.CookLevin.PolyManyOneRed`) to dense CNF-SAT
(`Cslib.Complexity.DenseSAT.denseSatDec`), and together with `denseSatDec_mem_NP` dense CNF-SAT is
NP-complete (`denseSatDec_npComplete`). The definitions of `P` and `NP` are not changed.

Given `L ∈ NP` with certificate bound `p` and verifier relation `R`, `IsPolyTime R` provides a
machine `V₀` reading the canonical encoding of `(x, w)`. Composed after
`DenseSAT.ToCanonical.computable`, it becomes a machine `V` reading `x # w` with one input
symbol per certificate bit. The ported tableau construction (`Package.gComp`) turns `V`, `p`
and a polynomial bound on `V`'s time into a reduction machine on raw input bits; composing it
between `DenseSAT.DecodeBits.computable` and `DenseSAT.EncodeBits.computable` gives the
`IsPolyTime` witness. Correctness is `v_correct`, from the tableau's `Assembly.phi_iff`.

This is NP-completeness of the **dense** SAT language. Cook-Levin for `Cslib.CookLevin.satDec`
(binary variable indices) is `SatVerifier.Machine.cook_levin_SAT_np_complete`.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Hardness

open MetaMathlibExt ComplexityTheory Cslib.Complexity.DenseSAT Cslib.Complexity.CookLevin.Situation
  Cslib.Complexity.CookLevin.Assembly Cslib.Complexity.CookLevin.Precompute
  Cslib.Complexity.CookLevin.Package Turing

/-! ## [POLY] Every polynomial is bounded by some `(j + c)^e` -/

theorem pow_weaken {j c e c' e' : ℕ} (hc : 1 ≤ c) (h1 : c ≤ c') (h2 : e ≤ e') :
    (j + c) ^ e ≤ (j + c') ^ e' :=
  (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) h2)

theorem eval_le_pow (p : Polynomial ℕ) : ∃ c e, 1 ≤ c ∧ ∀ j, p.eval j ≤ (j + c) ^ e := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨c1, e1, hc1, h1⟩ := hp
      obtain ⟨c2, e2, hc2, h2⟩ := hq
      refine ⟨c1 + c2, e1 + e2 + 1, by omega, fun j => ?_⟩
      have a1 := (h1 j).trans
        (pow_weaken (j := j) hc1 (Nat.le_add_right c1 c2) (Nat.le_add_right e1 e2))
      have a2 := (h2 j).trans
        (pow_weaken (j := j) hc2 (Nat.le_add_left c2 c1) (Nat.le_add_left e2 e1))
      have h2le : 2 ≤ j + (c1 + c2) := by omega
      rw [Polynomial.eval_add, pow_succ]
      calc p.eval j + q.eval j
          ≤ (j + (c1 + c2)) ^ (e1 + e2) + (j + (c1 + c2)) ^ (e1 + e2) := Nat.add_le_add a1 a2
        _ = (j + (c1 + c2)) ^ (e1 + e2) * 2 := by ring
        _ ≤ (j + (c1 + c2)) ^ (e1 + e2) * (j + (c1 + c2)) := Nat.mul_le_mul_left _ h2le
  | monomial n a =>
      refine ⟨a + 1, n + 1, by omega, fun j => ?_⟩
      rw [Polynomial.eval_monomial, pow_succ]
      calc a * j ^ n ≤ (j + (a + 1)) * (j + (a + 1)) ^ n :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) n)
        _ = _ := mul_comm _ _

/-! ## [LIST] Pulling a list back through a map -/

theorem pull {α β : Type} (f : α → β) (L : List α) :
    ∀ l : List β, (∀ z ∈ l, z ∈ L.map f) → ∃ l0 : List α, l0.map f = l
  | [], _ => ⟨[], rfl⟩
  | z :: l, h => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 (h z (by simp))
      obtain ⟨l0, rfl⟩ := pull f L l (fun w hw => h w (by simp [hw]))
      exact ⟨u :: l0, rfl⟩

/-! ## [ENC] An encoding whose output alphabet contains a chosen accept symbol -/

section Classical

open Classical

/-- `symSet` plus one extra symbol `acc` on the output stack. -/
noncomputable def symSetX (M : FinTM2) (acc : M.Γ M.k₁) (k : M.K) : Finset (M.Γ k) :=
  symSet M k ∪ (if h : M.k₁ = k then {cast (congrArg M.Γ h) acc} else ∅)

theorem acc_mem_symSetX (M : FinTM2) (acc : M.Γ M.k₁) : acc ∈ symSetX M acc M.k₁ := by
  unfold symSetX
  exact Finset.mem_union_right _ (by rw [dite_eq_left rfl]; exact Finset.mem_singleton_self _)

/-- `Enc.ofFinTM2` with `acc` added to the effective output alphabet. -/
noncomputable def encX (M : FinTM2) (acc : M.Γ M.k₁) : Enc M :=
  letI := M.kFin; letI := M.ΛFin; letI := M.σFin
  { KK := Fintype.card M.K
    kc := fun k => Fintype.equivFin M.K k
    kd := fun n => if h : n < Fintype.card M.K then (Fintype.equivFin M.K).symm ⟨n, h⟩ else M.k₀
    kc_lt := fun k => (Fintype.equivFin M.K k).2
    kd_kc := fun k => by simp
    kc_kd := fun n hn => by simp [hn]
    A0 := Fintype.card (Option M.Λ × M.σ)
    lc := fun x => Fintype.equivFin _ x
    ld := fun c => if h : c < Fintype.card (Option M.Λ × M.σ) then
      (Fintype.equivFin _).symm ⟨c, h⟩ else (none, M.initialState)
    lc_lt := fun x => (Fintype.equivFin _ x).2
    ld_lc := fun x => by rw [dite_eq_left (Fintype.equivFin _ x).2]; simp
    lc_ld := fun c hc => by rw [dite_eq_left hc]; simp
    sz := fun k => (symSetX M acc k).card
    dec := fun k i => ((symSetX M acc k).equivFin.symm i).1
    enc := fun k x => if h : x ∈ symSetX M acc k then (symSetX M acc k).equivFin ⟨x, h⟩ + 1 else 0
    enc_dec := fun k i => by simp
    push_mem := fun l k x h => ⟨(symSetX M acc k).equivFin
      ⟨x, Finset.mem_union_left _ (push_mem_symSet M l k x h)⟩, by simp⟩
    input_mem := fun x => ⟨(symSetX M acc M.k₀).equivFin
      ⟨x, Finset.mem_union_left _ (input_mem_symSet M x)⟩, by simp⟩ }

/-- The accept symbol is encodable: `phi_iff`'s `hacc`, unconditionally. -/
theorem encX_acc (M : FinTM2) (acc : M.Γ M.k₁) : ∃ i, (encX M acc).dec M.k₁ i = acc :=
  ⟨(symSetX M acc M.k₁).equivFin ⟨acc, acc_mem_symSetX M acc⟩, by simp [encX]⟩

end Classical

/-! ## The verifier's machine and the reduction's parameters -/

section Ver

variable {fv : List Bool × List Bool → Bool}
  (V : TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) fv)

/-- Accept symbol: the verifier's output symbol for `true`. -/
def vacc : V.tm.Γ V.tm.k₁ := V.outputAlphabet.symm true

/-- The tableau encoding of the verifier, with the accept symbol in its output alphabet. -/
noncomputable def vE : Enc V.tm := encX V.tm (vacc V)

/-- Raw input bits as symbols `Fin 2`. -/
noncomputable def veqv : Fin (Fintype.card Bool) ≃ Bool := (Fintype.equivFin Bool).symm

/-- Input bit `i` of `x`, as the verifier sees it (left-tagged). -/
noncomputable def vι (i : Fin (Fintype.card Bool)) : V.tm.Γ V.tm.k₀ :=
  V.inputAlphabet.symm (Sum.inl (veqv i))

/-- The separator `#`. -/
def vsep : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr none)

/-- Certificate bit `g`, right-tagged. -/
def vY (g : Bool) : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr (some g))

/-- All certificate symbols. -/
noncomputable def vYs : List (V.tm.Γ V.tm.k₀) := (Finset.univ : Finset Bool).toList.map (vY V)

/-- `T = (m + c)^e` dominates the verifier's time polynomial. -/
noncomputable def vc : ℕ := Classical.choose (eval_le_pow V.time)

/-- Exponent with `V.time.eval j ≤ (j + vc V) ^ ve V`. -/
noncomputable def ve : ℕ := Classical.choose (Classical.choose_spec (eval_le_pow V.time))

theorem v_time (j : ℕ) : V.time.eval j ≤ (j + vc V) ^ ve V :=
  (Classical.choose_spec (Classical.choose_spec (eval_le_pow V.time))).2 j

/-- The verifier's input on `(a, y)` is `x ++ (y mapped)`, `x` = tagged `a` then `#`. -/
theorem v_input (a y : List Bool) :
    List.map V.inputAlphabet.invFun (Verifier.pairEncode (a, y)) =
      (a.map veqv.invFun).map (vι V) ++ [vsep V] ++ y.map (vY V) := by
  unfold vι vsep vY
  simp [Verifier.pairEncode, Function.comp_def]
  exact ⟨fun _ => veqv.apply_symm_apply _, fun _ => veqv.apply_symm_apply _⟩

/-- Determinism link: from row `T` on, the verifier's run on `(a, y)` is its output. -/
theorem v_run (a y : List Bool) {T : ℕ} (hT : V.time.eval (a.length + 1 + y.length) ≤ T) :
    runI V.tm (initList V.tm ((a.map veqv.invFun).map (vι V) ++ [vsep V] ++ y.map (vY V))) T =
      haltList V.tm [V.outputAlphabet.symm (fv (a, y))] := by
  have h := V.outputsFun (a, y)
  rw [v_input] at h
  have hl : (Verifier.pairEncode (a, y)).length = a.length + 1 + y.length := by
    simp only [Verifier.pairEncode, List.length_append, List.length_cons, List.length_map]
    omega
  rw [hl] at h
  exact runI_haltList V.tm _ _ h hT

/-- The reduction function on raw input bits. -/
noncomputable def red (p : Polynomial ℕ) : List Bool → List Bool :=
  fR (vE V) (fun l : List Bool => l) veqv (vYs V) (vacc V) (vι V) (vsep V) p (vc V) (ve V)

/-- **Correctness of the reduction**: `L' a ↔ SAT (red a)`, for a language `L'` whose
certificates of length at most `p(|a|)` are checked by `fv`. -/
theorem v_correct {R : List Bool → List Bool → Prop} {p : Polynomial ℕ} {L' : List Bool → Prop}
    (hfv : ∀ q : List Bool × List Bool, R q.1 q.2 ↔ fv q = true)
    (hL : ∀ a, L' a ↔ ∃ y : List Bool, y.length ≤ p.eval a.length ∧ R a y) (a : List Bool) :
    L' a ↔ SAT (red V p a) := by
  set n := a.length with hn
  set s := a.map veqv.invFun with hs
  have hsl : s.length = n := by rw [hs, List.length_map]
  have hx : (s.map (vι V) ++ [vsep V]).length ≤ mOf p s.length := by
    simp only [List.length_append, List.length_map, List.length_singleton, mOf]; omega
  change L' a ↔ ∃ asg, cnfSat (decodeCNF (encodeCNF (Phi (vE V) (s.map (vι V) ++ [vsep V]) (vYs V)
    (vacc V) (mOf p s.length) (TOf p (vc V) (ve V) s.length)))) asg
  rw [decodeCNF_encodeCNF, phi_iff (vE V) hx (encX_acc _ _), hL, hsl]
  have hT : ∀ y : List Bool, n + 1 + y.length ≤ mOf p n →
      V.time.eval (n + 1 + y.length) ≤ TOf p (vc V) (ve V) n := fun y hy =>
    (TM2Composition.eval_mono _ hy).trans (v_time V _)
  have hacc : ∀ y : List Bool, n + 1 + y.length ≤ mOf p n →
      (Accepts V.tm (runI V.tm (initList V.tm (s.map (vι V) ++ [vsep V] ++ y.map (vY V)))
        (TOf p (vc V) (ve V) n)) (vacc V) ↔ fv (a, y) = true) := by
    intro y hy
    rw [hs, v_run V a y (hT y hy), accepts_haltList]
    simp [vacc]
  constructor
  · rintro ⟨y, hy, hR⟩
    rw [← hn] at hy
    have hyl : n + 1 + y.length ≤ mOf p n := by unfold mOf; omega
    refine ⟨y.map (vY V), fun z hz => ?_, ?_, (hacc y hyl).2 ((hfv (a, y)).1 hR)⟩
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hz
      exact List.mem_map.2 ⟨g, Finset.mem_toList.2 (Finset.mem_univ g), rfl⟩
    · simp only [List.length_append, List.length_map, List.length_singleton]; rw [hsl]; exact hyl
  · rintro ⟨y', hY, hlen, hA⟩
    obtain ⟨y, rfl⟩ := pull (vY V) _ y' hY
    have hyl : n + 1 + y.length ≤ mOf p n := by
      simp only [List.length_append, List.length_map, List.length_singleton] at hlen
      rw [hsl] at hlen; exact hlen
    refine ⟨y, by rw [← hn]; unfold mOf at hyl; omega, (hfv (a, y)).2 ((hacc y hyl).1 ?_)⟩
    exact hA

/-- The reduction is polynomial-time computable in formal-math's sense. -/
theorem isPolyTime_red (p : Polynomial ℕ) : IsPolyTime (red V p) := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable
    (gComp (vE V) (fun l : List Bool => l) veqv (vYs V) (vacc V) (vι V) (vsep V) p (vc V) (ve V))
  have h2 := tm2ComputableInPolyTime_comp h EncodeBits.computable
  exact h2

end Ver

/-! ## Hardness and completeness -/

/-- **Every NP problem reduces to dense CNF-SAT.** -/
theorem denseSatDec_npHard (L : DecisionProblem) (hL : L ∈ NP) :
    Cslib.CookLevin.PolyManyOneRed L denseSatDec := by
  obtain ⟨p, R, ⟨V₀⟩, hLR⟩ := hL
  let V : TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) (R ∘ id) :=
    TM2Composition.compComputable ToCanonical.computable V₀
  refine ⟨red V p, isPolyTime_red V p, fun x => ?_⟩
  have h := v_correct V (R := fun a y => R (a, y) = true) (L' := fun a => L a = true)
    (fun _ => Iff.rfl) hLR x
  classical
  rw [Bool.eq_iff_iff, denseSatDec, decide_eq_true_iff]
  exact h

/-- **Cook-Levin for dense CNF-SAT**: `denseSatDec` is NP-complete for the canonical classes,
with polynomial-time many-one reductions. -/
theorem denseSatDec_npComplete :
    denseSatDec ∈ NP ∧
      ∀ L : DecisionProblem, L ∈ NP → Cslib.CookLevin.PolyManyOneRed L denseSatDec :=
  ⟨denseSatDec_mem_NP, denseSatDec_npHard⟩

end Cslib.Complexity.CookLevin.Hardness
