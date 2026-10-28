/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.AssumptionFeeds.RungOneDichotomy
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Weight

/-!
# Few-forms common zero
Proves `RungOneDichotomy.FewFormsCommonZero`: `m` homogeneous positive-degree
forms in `N` variables (`m < N`), over an algebraically closed field, have a
common nonzero zero. This discharges residual R1 (§3-L2),
hence the `hL2` hypothesis of `hdichRung1_unhorth_of_commonZero`.

Route A' (Nullstellensatz + minimal-prime pin + coordinate chain): assume no
nonzero common zero; then
the locus of `J = span (range F)` is `{0}`, so every prime over `J` equals the
vanishing ideal `V₀` of `{0}` (strong Nullstellensatz); a minimal prime `P`
over `J` (which exists since `J ≠ ⊤`) satisfies `P.height ≤ card ι` (Krull's
Hauptidealsatz) while `(N : ℕ∞) ≤ V₀.height` (explicit coordinate chain of
primes), contradicting `card ι < N`.

No circularity: the proof uses only mathlib lemmas. The in-repo import above is
used solely to name the target `def` (one import direction, no cycle); no
in-repo lemma is used.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
open scoped BigOperators

/-! ## Step 0: homogeneous positive-degree forms vanish at zero -/

/-- Step 0: a homogeneous form of positive degree vanishes at `0`.
Uniform for `F = 0` (vacuous homogeneity, `coeff 0 = 0` anyway). -/
theorem eval_zero_of_isHomogeneous_of_pos_deg {N : ℕ} {K : Type*} [Field K]
    {F : MvPolynomial (Fin N) K} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : 1 ≤ d) :
    MvPolynomial.eval 0 F = 0 := by
  have hcc : F.constantCoeff = 0 := by
    rw [MvPolynomial.constantCoeff_eq]
    by_contra hne
    have hw := hF hne
    have hw0 : Finsupp.weight (1 : Fin N → ℕ) (0 : Fin N →₀ ℕ) = 0 := map_zero _
    omega
  rw [MvPolynomial.eval_zero]
  exact hcc

#print axioms eval_zero_of_isHomogeneous_of_pos_deg

/-! ## Coordinate-killing chain (Step 5 setup) -/

/-- Assignment killing the first `k` coordinates. -/
noncomputable def killBelow (N k : ℕ) {K : Type*} [CommSemiring K] :
    Fin N → MvPolynomial (Fin N) K :=
  fun i => if i.val < k then 0 else MvPolynomial.X i

/-- Endomorphism killing the first `k` coordinates. -/
noncomputable def killBelowHom (N k : ℕ) {K : Type*} [CommSemiring K] :
    MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (killBelow N k)

/-- Kernel of the coordinate-killing endomorphism. -/
noncomputable def killBelowKer (N k : ℕ) {K : Type*} [CommSemiring K] :
    Ideal (MvPolynomial (Fin N) K) :=
  RingHom.ker (killBelowHom N k)

/-- The set of killed coordinate functions. -/
def killedSpanSet (N k : ℕ) {K : Type*} [CommSemiring K] :
    Set (MvPolynomial (Fin N) K) :=
  { y | ∃ i : Fin N, i.val < k ∧ MvPolynomial.X i = y }

/-- Killed coordinates map to `0`. -/
theorem killBelow_eq_zero_of_lt (N k : ℕ) {K : Type*} [CommSemiring K]
    (i : Fin N) (hi : i.val < k) :
    killBelow N k i = (0 : MvPolynomial (Fin N) K) := by
  change (if i.val < k then (0 : MvPolynomial (Fin N) K)
    else MvPolynomial.X i) = 0
  simp [hi]

#print axioms killBelow_eq_zero_of_lt

/-- Surviving coordinates map to themselves. -/
theorem killBelow_eq_X_of_not_lt (N k : ℕ) {K : Type*} [CommSemiring K]
    (i : Fin N) (hi : ¬ i.val < k) :
    killBelow N k i = (MvPolynomial.X i : MvPolynomial (Fin N) K) := by
  change (if i.val < k then (0 : MvPolynomial (Fin N) K)
    else MvPolynomial.X i) = MvPolynomial.X i
  simp [hi]

#print axioms killBelow_eq_X_of_not_lt

/-- The endomorphism acts on generators by the assignment. -/
theorem killBelowHom_X (N k : ℕ) {K : Type*} [CommSemiring K] (i : Fin N) :
    killBelowHom N k ((MvPolynomial.X i : MvPolynomial (Fin N) K))
      = killBelow N k i := by
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C : K →+* MvPolynomial (Fin N) K) (killBelow N k)
    ((MvPolynomial.X i : MvPolynomial (Fin N) K)) = killBelow N k i
  exact MvPolynomial.eval₂Hom_X' _ _ _

#print axioms killBelowHom_X

/-- The `p - φ p ∈ span` induction: every polynomial differs from its
killed image by an element of the span of killed coordinates. -/
theorem sub_killBelowHom_mem_span (N k : ℕ) {K : Type*} [Field K]
    (p : MvPolynomial (Fin N) K) :
    p - killBelowHom N k p ∈ Ideal.span (killedSpanSet N k) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : killBelowHom N k (MvPolynomial.C a) = MvPolynomial.C a := by
        change MvPolynomial.eval₂Hom MvPolynomial.C (killBelow N k)
          (MvPolynomial.C a) = MvPolynomial.C a
        exact MvPolynomial.eval₂Hom_C _ _ _
      rw [hC, sub_self]
      exact Ideal.zero_mem _
  | add p q hp hq =>
      have hring : p + q - killBelowHom N k (p + q)
          = (p - killBelowHom N k p) + (q - killBelowHom N k q) := by
        rw [map_add]
        ring
      rw [hring]
      exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
      have hmul : killBelowHom N k (p * MvPolynomial.X n)
          = killBelowHom N k p * killBelow N k n := by
        rw [map_mul, killBelowHom_X]
      by_cases hn : n.val < k
      · have h0 : killBelow N k n = (0 : MvPolynomial (Fin N) K) :=
          killBelow_eq_zero_of_lt N k n hn
        rw [hmul, h0, mul_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, hn, rfl⟩)
      · have hX : killBelow N k n
            = (MvPolynomial.X n : MvPolynomial (Fin N) K) :=
          killBelow_eq_X_of_not_lt N k n hn
        rw [hmul, hX]
        have hring : p * MvPolynomial.X n - killBelowHom N k p * MvPolynomial.X n
            = (p - killBelowHom N k p) * MvPolynomial.X n := by ring
        rw [hring, mul_comm]
        exact Ideal.mul_mem_left _ _ hp

#print axioms sub_killBelowHom_mem_span

/-- The kernel is exactly the span of the killed coordinates. -/
theorem killBelowKer_eq_span (N k : ℕ) {K : Type*} [Field K] :
    (killBelowKer N k : Ideal (MvPolynomial (Fin N) K))
      = Ideal.span (killedSpanSet N k) := by
  apply le_antisymm
  · intro p hp
    have hmem := sub_killBelowHom_mem_span N k p
    rw [RingHom.mem_ker.mp hp] at hmem
    rwa [sub_zero] at hmem
  · rw [Ideal.span_le]
    rintro y ⟨i, hi, rfl⟩
    change (MvPolynomial.X i : MvPolynomial (Fin N) K)
      ∈ RingHom.ker (killBelowHom N k)
    rw [RingHom.mem_ker, killBelowHom_X, killBelow_eq_zero_of_lt N k i hi]

#print axioms killBelowKer_eq_span

/-- Each kernel is prime (target is a domain). -/
theorem killBelowKer_prime (N k : ℕ) {K : Type*} [Field K] :
    ((killBelowKer N k : Ideal (MvPolynomial (Fin N) K))).IsPrime :=
  RingHom.ker_isPrime (killBelowHom N k)

#print axioms killBelowKer_prime

/-- The chain is strict: `X ⟨k, _⟩` enters at step `k + 1`. -/
theorem killBelowKer_lt_succ (N k : ℕ) {K : Type*} [Field K] (hk : k < N) :
    (killBelowKer N k : Ideal (MvPolynomial (Fin N) K))
      < killBelowKer N (k + 1) := by
  have hle : (killBelowKer N k : Ideal (MvPolynomial (Fin N) K))
      ≤ killBelowKer N (k + 1) := by
    rw [killBelowKer_eq_span, killBelowKer_eq_span]
    apply Ideal.span_mono
    rintro y ⟨i, hi, rfl⟩
    exact ⟨i, lt_trans hi (lt_add_one k), rfl⟩
  have hne : (killBelowKer N k : Ideal (MvPolynomial (Fin N) K))
      ≠ killBelowKer N (k + 1) := by
    intro heq
    have hmem : (MvPolynomial.X (⟨k, hk⟩ : Fin N)
        : MvPolynomial (Fin N) K) ∈ killBelowKer N (k + 1) := by
      rw [killBelowKer_eq_span]
      exact Ideal.subset_span ⟨⟨k, hk⟩, lt_add_one k, rfl⟩
    rw [← heq] at hmem
    have hker := RingHom.mem_ker.mp hmem
    rw [killBelowHom_X,
      killBelow_eq_X_of_not_lt N k (⟨k, hk⟩ : Fin N) (lt_irrefl k)] at hker
    exact MvPolynomial.X_ne_zero _ hker
  exact lt_of_le_of_ne hle hne

#print axioms killBelowKer_lt_succ

/-- Step 0 of the chain is `⊥` (no coordinates killed). -/
theorem killBelowKer_zero (N : ℕ) {K : Type*} [Field K] :
    (killBelowKer N 0 : Ideal (MvPolynomial (Fin N) K)) = ⊥ := by
  rw [killBelowKer_eq_span]
  have hempty : (killedSpanSet N 0 : Set (MvPolynomial (Fin N) K)) = ∅ := by
    ext y
    constructor
    · rintro ⟨i, hi, _⟩
      exact absurd hi (Nat.not_lt_zero _)
    · intro hy
      exact absurd hy (Set.notMem_empty y)
  rw [hempty, Ideal.span_empty]

#print axioms killBelowKer_zero

/-- Height lower bound along the chain by strict iteration. -/
theorem natCast_le_height_killBelowKer (N k : ℕ) {K : Type*} [Field K]
    (hk : k ≤ N) : (k : ℕ∞)
      ≤ ((killBelowKer N k : Ideal (MvPolynomial (Fin N) K))).height := by
  revert hk
  induction k with
  | zero =>
      intro _
      rw [killBelowKer_zero, Ideal.height_bot, Nat.cast_zero]
  | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      have hk' : k ≤ N := by omega
      have ihk := ih hk'
      have hlt : (killBelowKer N k : Ideal (MvPolynomial (Fin N) K))
          < killBelowKer N (k + 1) := killBelowKer_lt_succ N k hkN
      have hPk : ((killBelowKer N k : Ideal (MvPolynomial (Fin N) K))).IsPrime :=
        killBelowKer_prime N k
      have hPk1 : ((killBelowKer N (k + 1)
          : Ideal (MvPolynomial (Fin N) K))).IsPrime :=
        killBelowKer_prime N (k + 1)
      have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have hcast : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := hcast
        _ ≤ ((killBelowKer N k : Ideal (MvPolynomial (Fin N) K))).height + 1 :=
          add_le_add_left ihk 1
        _ ≤ ((killBelowKer N (k + 1)
          : Ideal (MvPolynomial (Fin N) K))).height := hstep

#print axioms natCast_le_height_killBelowKer

/-- The top of the chain sits under the vanishing ideal of `{0}`. -/
theorem killBelowKer_le_vanishingIdeal_zero (N : ℕ) {K : Type*} [Field K] :
    killBelowKer N N
      ≤ MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K)) := by
  rw [killBelowKer_eq_span, Ideal.span_le]
  rintro y ⟨i, _, rfl⟩
  change MvPolynomial.X i
    ∈ MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K))
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  rw [MvPolynomial.aeval_X]
  rfl

#print axioms killBelowKer_le_vanishingIdeal_zero

/-- Step 5 conclusion: `(N : ℕ∞) ≤ V₀.height` via the coordinate chain. -/
theorem height_ge_of_coord_chain (N : ℕ) {K : Type*} [Field K] :
    (N : ℕ∞)
      ≤ (MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K))).height :=
  (natCast_le_height_killBelowKer N N le_rfl).trans
    (Ideal.height_mono (killBelowKer_le_vanishingIdeal_zero N))

#print axioms height_ge_of_coord_chain

/-! ## Main theorem: few-forms common zero -/

/-- L2 block: `m` homogeneous positive-degree forms in `N` variables,
`m < N`, over an algebraically closed field have a common nonzero zero.
Proves the proved `RungOneDichotomy.FewFormsCommonZero` def. -/
theorem fewFormsCommonZero (K : Type*) [Field K] [IsAlgClosed K] :
    RungOneDichotomy.FewFormsCommonZero K := by
  classical
  unfold RungOneDichotomy.FewFormsCommonZero
  intro N ι hI hcard F _d hhom hpos
  have h0 : ∀ j, MvPolynomial.eval (0 : Fin N → K) (F j) = 0 :=
    fun j => eval_zero_of_isHomogeneous_of_pos_deg (hhom j) (hpos j)
  have hJne : Ideal.span (Set.range F) ≠ ⊤ := by
    have hle : Ideal.span (Set.range F : Set (MvPolynomial (Fin N) K))
        ≤ MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K)) := by
      rw [Ideal.span_le]
      intro p hp
      obtain ⟨j, rfl⟩ := hp
      change F j ∈ MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K))
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      have hbr : MvPolynomial.aeval (0 : Fin N → K) (F j)
          = MvPolynomial.eval (0 : Fin N → K) (F j) := rfl
      rw [hbr]
      exact h0 j
    have hV0ne : MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K))
        ≠ ⊤ := by
      intro htop
      have hmem : MvPolynomial.C (1 : K)
          ∈ MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K)) := by
        rw [htop]
        exact Submodule.mem_top
      rw [MvPolynomial.mem_vanishingIdeal_iff] at hmem
      have h1 := hmem 0 rfl
      rw [MvPolynomial.aeval_C, map_one] at h1
      exact one_ne_zero h1
    intro htop
    rw [htop] at hle
    exact hV0ne (top_le_iff.mp hle)
  by_contra hcon
  have hlocus : MvPolynomial.zeroLocus K (Ideal.span (Set.range F))
      = ({0} : Set (Fin N → K)) := by
    rw [MvPolynomial.zeroLocus_span]
    ext x
    constructor
    · intro hx
      have hx' : ∀ p ∈ Set.range F, MvPolynomial.aeval x p = 0 := hx
      by_contra hx0
      have hxne : x ≠ 0 := fun h => hx0 (Set.mem_singleton_iff.mpr h)
      apply hcon
      refine ⟨x, hxne, fun j => ?_⟩
      have hbr : MvPolynomial.aeval x (F j) = MvPolynomial.eval x (F j) := rfl
      rw [← hbr]
      exact hx' (F j) ⟨j, rfl⟩
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change ∀ p ∈ Set.range F, MvPolynomial.aeval (0 : Fin N → K) p = 0
      intro p hp
      obtain ⟨j, rfl⟩ := hp
      have hbr : MvPolynomial.aeval (0 : Fin N → K) (F j)
          = MvPolynomial.eval (0 : Fin N → K) (F j) := rfl
      rw [hbr]
      exact h0 j
  have hstep3 : ∀ P : Ideal (MvPolynomial (Fin N) K),
      P.IsPrime → Ideal.span (Set.range F) ≤ P →
      P = MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K)) := by
    intro P hprime hle
    have hprimeI := hprime
    have hNS : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K P)
        = P :=
      MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P
    have hsub : MvPolynomial.zeroLocus K P ⊆ ({0} : Set (Fin N → K)) := by
      rw [← hlocus]
      exact MvPolynomial.zeroLocus_anti_mono hle
    have hcases := Set.subset_singleton_iff_eq.mp hsub
    rcases hcases with hempty | hzero
    · have h1 : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K P)
          = ⊤ := by
        rw [hempty]
        exact MvPolynomial.vanishingIdeal_empty
      rw [hNS] at h1
      exact absurd h1 hprime.ne_top
    · have h1 : MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K P)
          = MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K)) := by
        rw [hzero]
      rw [hNS] at h1
      exact h1
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hJne
  have hPprime : P.IsPrime := Ideal.IsMinimalPrime.isPrime hP
  have hPle : Ideal.span (Set.range F) ≤ P := Ideal.IsMinimalPrime.le hP
  have hPV0 : P = MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K)) :=
    hstep3 P hPprime hPle
  subst hPV0
  have hJeq : Ideal.span (Set.range F)
      = Ideal.span ((Finset.univ.image F :
        Finset (MvPolynomial (Fin N) K)) : Set _) := by
    congr 1
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hPmin : MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K)) ∈
      (Ideal.span ((Finset.univ.image F :
        Finset (MvPolynomial (Fin N) K)) : Set _)).minimalPrimes := by
    rw [← hJeq]
    exact hP
  have hNoethK : IsNoetherianRing K := PrincipalIdealRing.isNoetherianRing
  have hNoethMv : IsNoetherianRing (MvPolynomial (Fin N) K) :=
    MvPolynomial.isNoetherianRing
  have hupper : (MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K))).height
      ≤ ((Finset.univ.image F).card : ℕ∞) :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset hPmin
  have hcardle : (Finset.univ.image F).card ≤ Fintype.card ι := by
    rw [← Finset.card_univ]
    exact Finset.card_image_le
  have hlower : (N : ℕ∞)
      ≤ (MvPolynomial.vanishingIdeal K ({0} : Set (Fin N → K))).height :=
    height_ge_of_coord_chain N
  have hle : (N : ℕ∞) ≤ ((Fintype.card ι : ℕ) : ℕ∞) :=
    hlower.trans (hupper.trans (by exact_mod_cast hcardle))
  have hlt : ((Fintype.card ι : ℕ) : ℕ∞) < (N : ℕ∞) := by exact_mod_cast hcard
  exact lt_irrefl _ (lt_of_le_of_lt hle hlt)

#print axioms fewFormsCommonZero

/-- Unhorth rung-1 dichotomy, unconditional given realized algebra data:
`hdichRung1_unhorth_of_commonZero` discharged of `hL2` by
`fewFormsCommonZero`. No horth needed. -/
theorem hdichRung1_unhorth
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E) :
    JointAssembly.HdichRung1 n K c hn :=
  RungOneDichotomy.hdichRung1_unhorth_of_commonZero
    K E V n hn c b hexp hN htower hcomm (fewFormsCommonZero K)

#print axioms hdichRung1_unhorth

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
