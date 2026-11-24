/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Randomized
public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import MathlibExt.GameTheory.ZeroSumMinimax

/-!
# Yao's minimax principle for communication complexity

A randomized protocol is a finitely supported probability distribution on deterministic
protocols (public coins with an arbitrary distribution). Its cost is the largest depth in its
support, and its error on an input pair `(x, y)` is the probability that the protocol drawn
answers wrongly. For a distribution `μ` on input pairs, the distributional complexity
`distComplexity f μ ε` is the least depth of a deterministic protocol whose error, averaged over
`μ`, is at most `ε`.

`randComplexity_eq_iSup_distComplexity` is Yao's minimax principle for communication: the
randomized `ε`-error complexity equals the largest `μ`-distributional `ε`-error complexity
(A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 3.3). The inequality
`≥` is an averaging argument; the inequality `≤` applies von Neumann's minimax theorem, in its
saddle-point form `matrixGame_exists_isSaddlePointOn`, to the game between the input pairs and
the finitely many functions computed by protocols of a given depth.

`PublicCoinProtocol.toRandomized` views a public-coin protocol (uniform random string) as a
randomized protocol with the same error, and `randComplexity_eqFn_le` deduces from the
random-hash protocol that equality has randomized complexity at most `k + 1` with error
`2 ^ (-k)`.
-/

@[expose] public section

open Matrix Convexity

namespace MathlibExt.Computability.CommunicationComplexity

variable {X Y : Type*}

/-- **Error indicator of a protocol.** `1` if the protocol `p` answers wrongly on `(x, y)` for
the function `f`, and `0` if it answers correctly. -/
def errorIndicator (p : Protocol X Y) (f : X → Y → Bool) (x : X) (y : Y) : ℝ :=
  if p.eval x y = f x y then 0 else 1

private theorem errorIndicator_congr {p p' : Protocol X Y} (h : p.eval = p'.eval)
    (f : X → Y → Bool) (x : X) (y : Y) : errorIndicator p f x y = errorIndicator p' f x y := by
  simp [errorIndicator, h]

/-- **Randomized protocol.** A finitely supported probability distribution on deterministic
protocols: the protocol actually run is drawn from it, independently of the inputs, and both
parties see the draw (A. Rao and A. Yehudayoff, *Communication Complexity*, early draft,
Chapter 3: "a randomized protocol can be thought of as a distribution on deterministic
protocols"). -/
abbrev RandomizedProtocol (X Y : Type*) : Type _ :=
  StdSimplex ℝ (Protocol X Y)

namespace RandomizedProtocol

/-- **Cost of a randomized protocol.** The largest depth of a deterministic protocol in its
support. -/
def cost (P : RandomizedProtocol X Y) : ℕ :=
  P.weights.support.sup Protocol.depth

/-- **Error of a randomized protocol.** The probability that the drawn protocol answers wrongly
for `f` on the input pair `(x, y)`. -/
noncomputable def error (P : RandomizedProtocol X Y) (f : X → Y → Bool) (x : X) (y : Y) : ℝ :=
  P.weights.sum fun p w => w * errorIndicator p f x y

end RandomizedProtocol

/-- **A public-coin protocol as a randomized protocol.** The uniform distribution on the random
strings, pushed forward along `run`. -/
noncomputable def PublicCoinProtocol.toRandomized {R : Type*} [Fintype R] [Nonempty R]
    (P : PublicCoinProtocol X Y R) : RandomizedProtocol X Y :=
  (StdSimplex.barycenter (K := ℝ) (M := R)).map P.run

/-- **The two notions of error agree.** The error of a public-coin protocol, as a fraction of
random strings, is the error of the randomized protocol it defines. -/
theorem PublicCoinProtocol.error_toRandomized {R : Type*} [Fintype R] [Nonempty R]
    (P : PublicCoinProtocol X Y R) (f : X → Y → Bool) (x : X) (y : Y) :
    P.toRandomized.error f x y = (P.errorProb f x y : ℝ) := by
  classical
  simp only [toRandomized, RandomizedProtocol.error, StdSimplex.weights_map]
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  have hsum : ∑ r : R, errorIndicator (P.run r) f x y =
      ((Finset.univ.filter fun r => (P.run r).eval x y ≠ f x y).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : (P.run r).eval x y = f x y <;> simp [errorIndicator, h]
  simp only [StdSimplex.weights_barycenter_apply]
  rw [← Finset.mul_sum, hsum, PublicCoinProtocol.errorProb]
  push_cast
  ring

/-- **Cost of the induced randomized protocol.** It is at most the cost of the public-coin
protocol. -/
theorem PublicCoinProtocol.cost_toRandomized_le {R : Type*} [Fintype R] [Nonempty R]
    (P : PublicCoinProtocol X Y R) : P.toRandomized.cost ≤ P.cost := by
  classical
  refine Finset.sup_le fun q hq => ?_
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hq)
  exact P.depth_le_cost r

/-- **Randomized communication complexity.** `randComplexity f ε` is the least cost of a
randomized protocol whose error on every input pair is at most `ε` (A. Rao and A. Yehudayoff,
*Communication Complexity*, early draft, Chapter 3, "worst-case" error). For finite inputs and
`ε ≥ 0` such a protocol exists. If none meets the bound (for instance when `ε < 0`, or possibly
for infinite inputs), the value is `0` by the convention `sInf ∅ = 0`. -/
noncomputable def randComplexity (f : X → Y → Bool) (ε : ℝ) : ℕ :=
  sInf {c | ∃ P : RandomizedProtocol X Y, P.cost ≤ c ∧ ∀ x y, P.error f x y ≤ ε}

/-- **Randomized communication complexity of equality.** For every `n` and `k`, equality of
`n`-bit strings has randomized communication complexity at most `k + 1` with error `2 ^ (-k)`,
by the random-hash protocol (A. Rao and A. Yehudayoff, *Communication Complexity*, early draft,
Chapter 3, Figure 3.1); deterministically it needs `n + 1` bits for `n ≥ 1`
(`commComplexity_eqFn`). -/
theorem randComplexity_eqFn_le (n k : ℕ) : randComplexity (eqFn n) (1 / 2 ^ k) ≤ k + 1 := by
  refine Nat.sInf_le ⟨(eqHashProtocol n k).toRandomized,
    (PublicCoinProtocol.cost_toRandomized_le _).trans (cost_eqHashProtocol_le n k),
    fun x y => ?_⟩
  rw [PublicCoinProtocol.error_toRandomized]
  by_cases h : x = y
  · subst h
    rw [errorProb_eqHashProtocol_self]
    norm_num
  · rw [errorProb_eqHashProtocol_of_ne h]
    norm_num

/-- **Distributional error of a deterministic protocol.** For a distribution `μ` on input pairs,
the probability under `μ` that `p` answers wrongly for `f`. -/
noncomputable def distError [Fintype X] [Fintype Y] (μ : StdSimplex ℝ (X × Y))
    (p : Protocol X Y) (f : X → Y → Bool) : ℝ :=
  ∑ xy : X × Y, μ.weights xy * errorIndicator p f xy.1 xy.2

/-- **Distributional communication complexity.** `distComplexity f μ ε` is the least depth of a
deterministic protocol whose error under the input distribution `μ` is at most `ε` (A. Rao and
A. Yehudayoff, *Communication Complexity*, early draft, Chapter 3, "average-case" error; fixing
the random string, a randomized protocol does no better against a fixed distribution). For
`ε ≥ 0` such a protocol exists; otherwise the value is `0` by the convention `sInf ∅ = 0`. -/
noncomputable def distComplexity [Fintype X] [Fintype Y] (f : X → Y → Bool)
    (μ : StdSimplex ℝ (X × Y)) (ε : ℝ) : ℕ :=
  sInf {c | ∃ p : Protocol X Y, p.depth ≤ c ∧ distError μ p f ≤ ε}

variable [Fintype X] [Fintype Y]

private theorem distError_eq_zero {μ : StdSimplex ℝ (X × Y)} {p : Protocol X Y}
    {f : X → Y → Bool} (hp : p.Computes f) : distError μ p f = 0 := by
  simp [distError, errorIndicator, hp _ _]

private theorem distComplexity_le_depth {μ : StdSimplex ℝ (X × Y)} {ε : ℝ} (hε : 0 ≤ ε)
    {p : Protocol X Y} {f : X → Y → Bool} (hp : p.Computes f) :
    distComplexity f μ ε ≤ p.depth :=
  Nat.sInf_le ⟨p, le_rfl, (distError_eq_zero hp).le.trans hε⟩

private theorem exists_of_distComplexity {μ : StdSimplex ℝ (X × Y)} {ε : ℝ} (hε : 0 ≤ ε)
    (f : X → Y → Bool) :
    ∃ p : Protocol X Y, p.depth ≤ distComplexity f μ ε ∧ distError μ p f ≤ ε := by
  obtain ⟨p, hp⟩ := Protocol.exists_computes f
  exact Nat.sInf_mem (s := {c | ∃ p : Protocol X Y, p.depth ≤ c ∧ distError μ p f ≤ ε})
    ⟨_, p, le_rfl, (distError_eq_zero hp).le.trans hε⟩

private theorem bddAbove_distComplexity {ε : ℝ} (hε : 0 ≤ ε) (f : X → Y → Bool) :
    BddAbove (Set.range fun μ : StdSimplex ℝ (X × Y) => distComplexity f μ ε) := by
  obtain ⟨p, hp⟩ := Protocol.exists_computes f
  exact ⟨p.depth, by rintro _ ⟨μ, rfl⟩; exact distComplexity_le_depth hε hp⟩

/-- Averaging: if a distribution averages `h` to at most `ε`, some point of its support has
`h ≤ ε`. -/
private theorem exists_mem_support_le {α : Type*} (P : StdSimplex ℝ α) (h : α → ℝ) {ε : ℝ}
    (hP : (P.weights.sum fun a w => w * h a) ≤ ε) : ∃ a ∈ P.weights.support, h a ≤ ε := by
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  have hsupp : P.weights.support.Nonempty := P.support_weights_nonempty
  have hlt : ∑ a ∈ P.weights.support, P.weights a * ε <
      ∑ a ∈ P.weights.support, P.weights a * h a :=
    Finset.sum_lt_sum_of_nonempty hsupp fun a ha =>
      mul_lt_mul_of_pos_left (hne a ha)
        (lt_of_le_of_ne (P.weights_nonneg a) (Ne.symm (Finsupp.mem_support_iff.1 ha)))
  rw [← Finset.sum_mul] at hlt
  have htot : ∑ a ∈ P.weights.support, P.weights a = 1 := P.total
  rw [htot, one_mul] at hlt
  exact absurd hP (not_le.2 hlt)

/-- **Distributional complexity is at most randomized complexity.** Against any input
distribution `μ`, some deterministic protocol in the support of an optimal randomized protocol
has `μ`-error at most `ε` (the easy direction of A. Rao and A. Yehudayoff, *Communication
Complexity*, early draft, Theorem 3.3). -/
theorem distComplexity_le_randComplexity (f : X → Y → Bool) (μ : StdSimplex ℝ (X × Y))
    {ε : ℝ} (hε : 0 ≤ ε) : distComplexity f μ ε ≤ randComplexity f ε := by
  obtain ⟨p₀, hp₀⟩ := Protocol.exists_computes f
  obtain ⟨P, hcost, herr⟩ := Nat.sInf_mem
    (s := {c | ∃ P : RandomizedProtocol X Y, P.cost ≤ c ∧ ∀ x y, P.error f x y ≤ ε})
    ⟨_, StdSimplex.single p₀, le_rfl, fun x y => by
      simp [RandomizedProtocol.error, errorIndicator, hp₀ x y, hε]⟩
  have havg : (P.weights.sum fun p w => w * distError μ p f) ≤ ε := by
    have hswap : (P.weights.sum fun p w => w * distError μ p f) =
        ∑ xy : X × Y, μ.weights xy * P.error f xy.1 xy.2 := by
      simp only [Finsupp.sum, distError, RandomizedProtocol.error, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun xy _ => Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [hswap]
    calc ∑ xy : X × Y, μ.weights xy * P.error f xy.1 xy.2
        ≤ ∑ xy : X × Y, μ.weights xy * ε :=
          Finset.sum_le_sum fun xy _ =>
            mul_le_mul_of_nonneg_left (herr xy.1 xy.2) (μ.weights_nonneg xy)
      _ = ε := by rw [← Finset.sum_mul, μ.total_of_fintype, one_mul]
  obtain ⟨p, hp, hpε⟩ := exists_mem_support_le P (fun p => distError μ p f) havg
  have h₁ : distComplexity f μ ε ≤ p.depth := Nat.sInf_le ⟨p, le_rfl, hpε⟩
  exact h₁.trans ((Finset.le_sup hp).trans hcost)

open Classical in
/-- **Yao's minimax principle for communication complexity.** For finite input sets and
`ε ≥ 0`, the randomized communication complexity of `f` with error at most `ε` on every input
equals the largest, over distributions `μ` on input pairs, of the least depth of a deterministic
protocol with error at most `ε` under `μ` (A. Rao and A. Yehudayoff, *Communication Complexity*,
early draft, Theorem 3.3, proved there from von Neumann's minimax theorem). -/
theorem randComplexity_eq_iSup_distComplexity (f : X → Y → Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    randComplexity f ε = ⨆ μ : StdSimplex ℝ (X × Y), distComplexity f μ ε := by
  refine le_antisymm ?_ ?_
  · set c := ⨆ μ : StdSimplex ℝ (X × Y), distComplexity f μ ε
    -- a deterministic representative, of depth at most `c`, for each function
    let rep : (X → Y → Bool) → Protocol X Y := fun g =>
      if h : ∃ p : Protocol X Y, p.depth ≤ c ∧ p.eval = g then h.choose else .output false
    have rep_depth (g) : (rep g).depth ≤ c := by
      simp only [rep]; split_ifs with h
      · exact h.choose_spec.1
      · simp [Protocol.depth]
    have rep_eval (p : Protocol X Y) (hp : p.depth ≤ c) : (rep p.eval).eval = p.eval := by
      have h : ∃ q : Protocol X Y, q.depth ≤ c ∧ q.eval = p.eval := ⟨p, hp, rfl⟩
      simp only [rep, h, ↓reduceDIte]
      exact h.choose_spec.2
    refine Nat.sInf_le ?_
    rcases isEmpty_or_nonempty (X × Y) with hI | hI
    · exact ⟨StdSimplex.single (.output false), by simp [RandomizedProtocol.cost,
        Protocol.depth], fun x y => (hI.false (x, y)).elim⟩
    let eI := Fintype.equivFin (X × Y)
    let eA := Fintype.equivFin (X → Y → Bool)
    have hn : 0 < Fintype.card (X × Y) := Fintype.card_pos
    have hm : 0 < Fintype.card (X → Y → Bool) := Fintype.card_pos
    let A : Matrix (Fin (Fintype.card (X × Y))) (Fin (Fintype.card (X → Y → Bool))) ℝ :=
      fun i j => errorIndicator (rep (eA.symm j)) f (eI.symm i).1 (eI.symm i).2
    obtain ⟨p, q, hp, hq⟩ := matrixGame_exists_isSaddlePointOn hn hm A
    -- the input distribution of the saddle point, and a good protocol against it
    let μ : StdSimplex ℝ (X × Y) := p.map eI.symm
    obtain ⟨p₀, hp₀, hp₀ε⟩ := exists_of_distComplexity (μ := μ) hε f
    have hp₀c : p₀.depth ≤ c := hp₀.trans (le_ciSup (bddAbove_distComplexity hε f) μ)
    have hsingle (v : Fin (Fintype.card (X → Y → Bool)) → ℝ) (i) :
        ((StdSimplex.single i : StdSimplex ℝ (Fin (Fintype.card (X × Y)))).weights :
          Fin (Fintype.card (X × Y)) → ℝ) ⬝ᵥ (A *ᵥ v) = (A *ᵥ v) i := by
      simp [StdSimplex.weights_single, Finsupp.single_eq_pi_single, single_dotProduct]
    have hcol (i) : (A *ᵥ (Pi.single (eA p₀.eval) (1 : ℝ))) i =
        errorIndicator p₀ f (eI.symm i).1 (eI.symm i).2 := by
      rw [mulVec_single_one]
      change errorIndicator (rep (eA.symm (eA p₀.eval))) f (eI.symm i).1 (eI.symm i).2 = _
      rw [Equiv.symm_apply_apply]
      exact errorIndicator_congr (rep_eval p₀ hp₀c) f _ _
    have hval : (p.weights : Fin (Fintype.card (X × Y)) → ℝ) ⬝ᵥ (A *ᵥ q.weights) ≤ ε := by
      refine (hq (StdSimplex.single (eA p₀.eval))).trans (le_of_eq_of_le ?_ hp₀ε)
      rw [StdSimplex.weights_single, Finsupp.single_eq_pi_single]
      simp only [dotProduct, hcol, distError, μ, StdSimplex.weights_map,
        Finsupp.mapDomain_equiv_apply, Equiv.symm_symm]
      exact Fintype.sum_equiv eI.symm _ _ fun i => by simp
    refine ⟨q.map fun j => rep (eA.symm j), ?_, fun x y => ?_⟩
    · refine Finset.sup_le fun r hr => ?_
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hr)
      exact rep_depth _
    · have hi := (hp (StdSimplex.single (eI (x, y)))).trans hval
      rw [hsingle] at hi
      refine le_of_eq_of_le ?_ hi
      simp only [RandomizedProtocol.error, StdSimplex.weights_map]
      rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
        Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
      simp only [mulVec, dotProduct, A, Equiv.symm_apply_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rcases isEmpty_or_nonempty (StdSimplex ℝ (X × Y)) with h | h
    · simp
    · exact ciSup_le fun μ => distComplexity_le_randComplexity f μ hε

end MathlibExt.Computability.CommunicationComplexity
