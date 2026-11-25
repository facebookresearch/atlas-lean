/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported and adapted by Adam Kiezun and Metamate.

The helper lemmas (`eval_le_pow`, `pull`, `encX`) and the shape of `v_correct` are adapted from the
final section of `Pkg.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Pkg.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: the verifier, the certificate bound and
the reduction are restated against formal-math's `MetaMathlibExt.ComplexityTheory.NP`,
`IsPolyTime` and `Cslib.CookLevin.PolyManyOneRed` (the source used its own `Millennium`
definitions): the certificate bound is an arbitrary polynomial `p` (the precomputation evaluates it
by Horner's rule), and the verifier and the reduction are wrapped in encoding-converter machines.
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

/-- **Effective alphabets with an adjoined accept symbol.** For a finite multi-stack Turing
machine $M$, a symbol $a$ of its output-stack alphabet and a stack $k$, this is the finite set of
symbols that some statement of $M$ can push on stack $k$ (together with the whole input alphabet
when $k$ is the input stack), with $a$ added when $k$ is the output stack. -/
noncomputable def symSetX (M : FinTM2) (acc : M.Γ M.k₁) (k : M.K) : Finset (M.Γ k) :=
  symSet M k ∪ (if h : M.k₁ = k then {cast (congrArg M.Γ h) acc} else ∅)

theorem acc_mem_symSetX (M : FinTM2) (acc : M.Γ M.k₁) : acc ∈ symSetX M acc M.k₁ := by
  unfold symSetX
  exact Finset.mem_union_right _ (by rw [dite_eq_left rfl]; exact Finset.mem_singleton_self _)

/-- **Tableau encoding with a chosen accept symbol.** Given a finite multi-stack Turing machine
$M$ and a symbol $a$ of its output-stack alphabet, this is the encoding of $M$ that numbers the
stacks and the pairs (optional label, state) through their finite enumerations, and whose
effective alphabet on each stack $k$ is the set of symbols some statement of $M$ can push on $k$
(plus the whole input alphabet if $k$ is the input stack), with $a$ added if $k$ is the output
stack. A symbol in that set has code one more than its position in it; any other symbol has
code $0$. -/
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

/-- **The chosen accept symbol is encodable.** Let $M$ be a finite multi-stack Turing machine and
let $a$ be a symbol of its output-stack alphabet. In the tableau encoding of $M$ with $a$ adjoined
to the output alphabet, some index of the effective output-stack alphabet decodes to $a$.

This discharges, for every machine, the accept-symbol hypothesis of the correctness theorem for
the assembled formula. -/
theorem encX_acc (M : FinTM2) (acc : M.Γ M.k₁) : ∃ i, (encX M acc).dec M.k₁ i = acc :=
  ⟨(symSetX M acc M.k₁).equivFin ⟨acc, acc_mem_symSetX M acc⟩, by simp [encX]⟩

end Classical

/-! ## The verifier's machine and the reduction's parameters -/

section Ver

variable {fv : List Bool × List Bool → Bool}
  (V : TM2ComputableInPolyTime Verifier.pairEncode (fun b : Bool => [b]) fv)

/-- **Accept symbol of the verifier.** Let $V$ be a polynomial-time machine computing a function
of pairs of bit lists from their pair encoding, whose output alphabet is identified with the
Booleans. The accept symbol is the output symbol of $V$ that corresponds to $\mathrm{true}$. -/
def vacc : V.tm.Γ V.tm.k₁ := V.outputAlphabet.symm true

/-- **Tableau encoding of the verifier.** For a polynomial-time Turing machine $V$ that computes a
Boolean function on pairs of bit strings, reading a pair $(a, y)$ as the bits of $a$, a separator,
then the bits of $y$, and writing its answer as one bit, this is the tableau encoding of $V$ whose
effective output alphabet is enlarged by the accept symbol: the output symbol of $V$ for true. -/
noncomputable def vE : Enc V.tm := encX V.tm (vacc V)

/-- **Bits as indices.** The bijection from $\{0, 1\}$, the indices below the number $2$ of
Booleans, onto the Booleans that is inverse to the fixed enumeration of the Booleans. -/
noncomputable def veqv : Fin (Fintype.card Bool) ≃ Bool := (Fintype.equivFin Bool).symm

/-- **Input-bit symbol of the verifier.** Let $V$ be a polynomial-time machine computing a
function of pairs of bit lists from their pair encoding, whose input alphabet is identified with
the pair alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$, and let $\beta$ be the
fixed bijection from $\{0, 1\}$ onto the Booleans. For an index $i \in \{0, 1\}$, this is the
symbol of $V$'s input alphabet that corresponds to the left-tagged bit $\mathrm{inl}(\beta(i))$. -/
noncomputable def vι (i : Fin (Fintype.card Bool)) : V.tm.Γ V.tm.k₀ :=
  V.inputAlphabet.symm (Sum.inl (veqv i))

/-- **Separator symbol of the verifier.** Let $V$ be a polynomial-time machine computing a
function of pairs of bit lists from their pair encoding, whose input alphabet is identified with
the pair alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$. This is the symbol of
$V$'s input alphabet that corresponds to the separator $\#$, the element
$\mathrm{inr}(\mathrm{none})$. -/
def vsep : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr none)

/-- **Certificate symbol of the verifier.** Let $V$ be a polynomial-time machine computing a
function of pairs of bit lists from their pair encoding, whose input alphabet is identified with
the pair alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$. For a bit $g$, this is the
symbol of $V$'s input alphabet that corresponds to the right-tagged bit
$\mathrm{inr}(\mathrm{some}\ g)$. -/
def vY (g : Bool) : V.tm.Γ V.tm.k₀ := V.inputAlphabet.symm (Sum.inr (some g))

/-- **Certificate symbols of the verifier.** Let $V$ be a polynomial-time machine computing a
function of pairs of bit lists from their pair encoding, whose input alphabet is identified with
the pair alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$. This is the list of the
symbols of $V$'s input alphabet corresponding to the right-tagged bits
$\mathrm{inr}(\mathrm{some}\ g)$ for $g = \mathrm{true}$ and $g = \mathrm{false}$, each once, in
the order of a fixed enumeration of the Booleans. -/
noncomputable def vYs : List (V.tm.Γ V.tm.k₀) := (Finset.univ : Finset Bool).toList.map (vY V)

/-- **Offset of the verifier's time bound.** Let $V$ be a polynomial-time machine computing a
function of pairs of bit lists from their pair encoding, with time polynomial $t_V$. This is a
natural number $c \ge 1$, fixed by choice, such that for some exponent $e$ we have
$t_V(j) \le (j + c)^e$ for every natural number $j$. -/
noncomputable def vc : ℕ := Classical.choose (eval_le_pow V.time)

/-- **Exponent of the verifier's time bound.** Let $V$ be a polynomial-time machine computing a
function of pairs of bit lists from their pair encoding, with time polynomial $t_V$, and let
$c \ge 1$ be the offset of its time bound, fixed by choice so that some exponent works. This is
an exponent $e$, fixed by choice, with $t_V(j) \le (j + c)^e$ for every natural number $j$. -/
noncomputable def ve : ℕ := Classical.choose (Classical.choose_spec (eval_le_pow V.time))

theorem v_time (j : ℕ) : V.time.eval j ≤ (j + vc V) ^ ve V :=
  (Classical.choose_spec (Classical.choose_spec (eval_le_pow V.time))).2 j

/-- **Input of the verifier on a pair.** Let $V$ be a polynomial-time machine computing a function
of pairs of bit lists from their pair encoding, whose input alphabet is identified with the pair
alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$, and let $\beta$ be the fixed
bijection from $\{0, 1\}$ onto the Booleans. For bit lists $a$ and $y$, translating the pair
encoding $a \# y$ symbol by symbol into $V$'s input alphabet gives the input-bit symbols of the
indices $\beta^{-1}(b)$ for the bits $b$ of $a$ in order, then the separator symbol, then the
certificate symbols of the bits of $y$ in order. -/
theorem v_input (a y : List Bool) :
    List.map V.inputAlphabet.invFun (Verifier.pairEncode (a, y)) =
      (a.map veqv.invFun).map (vι V) ++ [vsep V] ++ y.map (vY V) := by
  unfold vι vsep vY
  simp [Verifier.pairEncode, Function.comp_def]
  exact ⟨fun _ => veqv.apply_symm_apply _, fun _ => veqv.apply_symm_apply _⟩

/-- **The verifier's run settles on its output.** Let $V$ be a machine that computes a function
$f_v$ of pairs of bit lists from their pair encoding, within $t_V(n)$ steps on an encoding of
length $n$ for a polynomial $t_V$ with natural-number coefficients, with input alphabet
identified with the pair alphabet $\mathrm{Bool} \oplus \mathrm{Option}\ \mathrm{Bool}$ and output
alphabet identified with the Booleans. Let $a$, $y$ be bit lists of lengths $|a|$, $|y|$, and $T$ a
natural number with $t_V(|a| + 1 + |y|) \le T$. Start $V$ in its initial configuration with its
input stack holding the symbols for the left-tagged bits $\mathrm{inl}(b)$ of $a$, then the
separator $\mathrm{inr}(\mathrm{none})$, then the symbols for the right-tagged bits
$\mathrm{inr}(\mathrm{some}\ b)$ of $y$, and run it for $T$ steps, a halted configuration staying
unchanged. The result is the halted configuration, in the initial internal state, whose output
stack holds exactly the one output symbol for $f_v(a, y)$ and whose other stacks are empty. -/
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

/-- **The Cook–Levin reduction.** Let $V$ be a polynomial-time Turing machine that computes a
Boolean function on pairs of bit strings, reading a pair $(a, y)$ as the bits of $a$, a separator,
then the bits of $y$, and writing its answer as one bit; let $t$ be its time bound and fix
constants $c \ge 1$ and $e$ with $t(j) \le (j + c)^e$ for all $j$. For a polynomial $p$ with
natural-number coefficients, the reduction sends a bit string $a$ of length $n$ to the dense bit
encoding of the tableau formula $\Phi$ of $V$, built with the encoding of $V$ whose output
alphabet contains the output symbol $\mathrm{acc}$ for true, for the input prefix $x$ made of the
bits of $a$ followed by the separator, the certificate symbols of $V$ (one per bit) as the
allowed symbols after $x$, the accept symbol $\mathrm{acc}$, width $m = n + 1 + p(n)$ and
$T = (m + c)^e$ steps. -/
noncomputable def red (p : Polynomial ℕ) : List Bool → List Bool :=
  fR (vE V) (fun l : List Bool => l) veqv (vYs V) (vacc V) (vι V) (vsep V) p (vc V) (ve V)

/-- **Correctness of the reduction.** Let $V$ be a polynomial-time Turing machine that computes a
Boolean function $f$ on pairs of bit strings, reading a pair $(a, y)$ as the bits of $a$, a
separator, then the bits of $y$, and writing its answer as one bit. Let $p$ be a polynomial with
natural-number coefficients, $R$ a relation on bit strings with $R(a, y)$ iff $f(a, y)$ is true,
and $L'$ a predicate on bit strings such that $L'(a)$ holds iff some bit string $y$ of length at
most $p(|a|)$ satisfies $R(a, y)$. Then for every bit string $a$, $L'(a)$ holds iff the image of
$a$ under the reduction built from $V$ and $p$ is in CNF-SAT. -/
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

/-- **The Cook–Levin reduction is polynomial-time.** Let $V$ be a polynomial-time Turing machine
that computes a Boolean function on pairs of bit strings, reading a pair $(a, y)$ as the bits of
$a$, a separator, then the bits of $y$, and writing its answer as one bit. For every polynomial
$p$ with natural-number coefficients, the reduction built from $V$ and $p$ is polynomial-time
computable with respect to the canonical bit-string encodings. -/
theorem isPolyTime_red (p : Polynomial ℕ) : IsPolyTime (red V p) := by
  obtain ⟨h⟩ := tm2ComputableInPolyTime_comp DecodeBits.computable
    (gComp (vE V) (fun l : List Bool => l) veqv (vYs V) (vacc V) (vι V) (vsep V) p (vc V) (ve V))
  have h2 := tm2ComputableInPolyTime_comp h EncodeBits.computable
  exact h2

end Ver

/-! ## Hardness and completeness -/

/-- **Every NP problem reduces to dense CNF-SAT.** Every decision problem $L$ in NP has a
polynomial-time many-one reduction to dense CNF-SAT: a polynomial-time computable map $f$ on bit
strings such that, for every bit string $x$, $L$ accepts $x$ exactly when dense CNF-SAT accepts
$f(x)$. -/
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

/-- **Cook-Levin for dense CNF-SAT.** Dense CNF-SAT is NP-complete: it lies in NP, and every
decision problem in NP has a polynomial-time many-one reduction to dense CNF-SAT. -/
theorem denseSatDec_npComplete :
    denseSatDec ∈ NP ∧
      ∀ L : DecisionProblem, L ∈ NP → Cslib.CookLevin.PolyManyOneRed L denseSatDec :=
  ⟨denseSatDec_mem_NP, denseSatDec_npHard⟩

end Cslib.Complexity.CookLevin.Hardness
