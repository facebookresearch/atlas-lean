/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Data.ENat.SuccOrder
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.FiltrationStability
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GatedDischarge
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.SystemOfParametersWiring
import Appendix_FixedPoint.BezoutChain.Regularity.HomologicalDepth.WitnessKernelDimTwo

/-!
# Graded Nakayama bank for `GrDimGe2`
Banks the graded infrastructure that `GrDimGe2D2AtAss` (`dim gr ≥ 2` at
embdim 2, `GatedDischarge` §1) needs, and attacks it with the bank.

## What proves

* (§0) `grRegular Q` is nontrivial (via the degree-0 identification
  `grPiece_zero_equiv_quotient` with the residue field).
* (§1) The irrelevant ideal `grPlus` (span of positive-degree homogeneous
  elements) + its API: the `grOf`/`grCoeff` insulation layer over
  `DirectSum`, the key graded-ring computation
  `gr_mul_coeff_zero_of_right` (degree-0 part of a product vanishes when
  the right factor has no degree-0 part), degree-0-component vanishing
  on `grPlus`, `grPlus_ne_top`.
* (§2) The filtration link (GT's scoped graded half, forward direction):
  `grPlus^N = ⊥ → 𝔪^N ≤ 𝔪^{N+1}` (via `gr_of_mem_grPlus_pow`: every
  degree-`N` class lifts into `grPlus^N`, by span induction generalizing
  `grPiece_span_mul_eq_top`), hence `grPlus^N = ⊥ → dim R_Q = 0` (reusing
  the GatedDischarge R-side collapse), hence at embdim 2
  `∀ N, grPlus^N ≠ ⊥`.
* (§3) The reverse direction + Artinian-collapse reuse: `𝔪^N = ⊥ →
  grPlus^N = ⊥` (via `grPlus_pow_le_span_ge`: `grPlus^N` is spanned by
  homogeneous elements of degree `≥ N`), hence `dim R_Q = 0 →
  ∃ N, grPlus^N = ⊥` (Hopkins–Levitzki + nilpotent maximal ideal), hence
  the unconditional iff `grPlus_pow_eq_bot_iff_dim_eq_zero`.
* (§4) Graded Nakayama factored through Mathlib Nakayama:
  `graded_nakayama_of_le_jacobson` closes the Mathlib side
  unconditionally; the remaining hypothesis `grPlus ≤ jacobson ⊥` is
  where homogeneous data enters (gap-gn-1, scoped — false ungraded in
  general, e.g. `κ[t]` with the maximal ideal `(t - 1)`).
* (§5) Homogeneous ideals/primes for our `gr` (self-contained component
  definitions, since Mathlib's `GradedRing` decomposition API does not
  apply to `associatedGraded` directly): `grPlus` is homogeneous;
  homogeneous-component extraction; the homogeneous properness lemma
  `P ⊔ span{h} ≠ ⊤`; order lemmas; and the attack masters:
  `grDimGe1_of_homogeneousAvoid` and `grDimGe2_of_homogeneousNonminAvoid`
  (conditional-exact on the homogeneous-avoidance SPECs), the Ass-level
  `grDimGe2D2_of_homogeneousNonminAvoid` concluding GT's
  `GrDimGe2D2AtAss`, and the downstream `hkerD2_of_homogeneousNonminAvoid`.
* (§6) Doc-only gap-gn register (graded Nakayama proper, homogeneous
  minimal primes, avoidance discharge) + residual register.

## Status

* §§0–3: unconditional (banked infrastructure + the filtration-link iff).
* §4: conditional-exact on `[grPlus ≤ jacobson ⊥]` (Mathlib-Nakayama side
  closed; hypothesis is gap-gn-1).
* §5: homogeneous API unconditional; attack masters conditional-exact on
  the homogeneous-avoidance SPECs (strictly narrower than `GrDimGe2`: a
  single structured-prime existence per prime vs the dimension
  inequality; the `0`-slice is discharged by §2–§3 through
  `grPlus^N ≠ ⊥`, and the masters need no upper-bound input).
* Overall: partial (bank proved + attack conditional-exact).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedNakayamaBank

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

open scoped Pointwise

variable (R : Type*) [CommRing R] (I : Ideal R)

/-! ## §0. `gr` is nontrivial -/

/-- The residue field at a prime is nontrivial (`1 ∈ 𝔪` would make the
maximal ideal `⊤`).
-/
instance residue_nontrivial_atPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Nontrivial (Localization.AtPrime Q ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)) := by
  refine ⟨1, 0, ?_⟩
  intro h10
  have hne := FiltrationStability.maximalIdeal_atPrime_ne_top Q
  apply hne
  rw [Ideal.eq_top_iff_one]
  have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)) (1 : Localization.AtPrime Q) = 0 := by
    rw [map_one]
    exact h10
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmk

#print axioms residue_nontrivial_atPrime

/-- The graded unit is nonzero in degree 0 (via the M4a identification
with the residue field).
-/
theorem grPiece_gOne_ne_zero [Nontrivial (R ⧸ I)] :
    (GradedMonoid.GOne.one : grPiece R I 0) ≠ 0 := by
  intro h
  have h1 : (grPiece_zero_equiv_quotient R I) GradedMonoid.GOne.one = 1 := by
    change grPiece_zero_to_quotient R I GradedMonoid.GOne.one = 1
    rw [grOne_eq_mk, grPiece_zero_to_quotient_mk]
    exact map_one _
  have h0 : (1 : R ⧸ I) = 0 := by
    rw [← h1, h]
    exact map_zero _
  exact one_ne_zero h0

#print axioms grPiece_gOne_ne_zero

/-! ## §1. The `grOf`/`grCoeff` layer, the irrelevant ideal, and its API

`associatedGraded` is a plain def unfolding to `DirectSum`, so raw
`DirectSum.of` terms (DirectSum-typed) and ideal operations
(associatedGraded-typed) do not mix. The `grOf`/`grCoeff` wrappers keep
every statement in the associatedGraded type. -/

/-- Homogeneous embedding into `gr` (associatedGraded-typed). -/
def grOf (n : ℕ) (a : grPiece R I n) : associatedGraded R I :=
  DirectSum.of (grPiece R I) n a

/-- Identity to the `DirectSum` type (gives a syntactic `DirectSum`
type, which bare ascriptions do not). -/
def toDirectSum (y : associatedGraded R I) : DirectSum ℕ (grPiece R I) :=
  y

/-- Degree-`n` component of a `gr` element. -/
def grCoeff (y : associatedGraded R I) (n : ℕ) : grPiece R I n :=
  (toDirectSum R I y) n

/-- `grOf` multiplies by adding degrees.
-/
theorem grOf_mul (i j : ℕ) (a : grPiece R I i) (b : grPiece R I j) :
    grOf R I i a * grOf R I j b =
      grOf R I (i + j) (GradedMonoid.GMul.mul a b) :=
  DirectSum.of_mul_of (A := grPiece R I) a b

#print axioms grOf_mul

/-- `grOf` sends `0` to `0`.
-/
theorem grOf_zero (n : ℕ) : grOf R I n 0 = 0 :=
  map_zero (DirectSum.of (grPiece R I) n)

#print axioms grOf_zero

/-- `grOf` commutes with addition.
-/
theorem grOf_add (n : ℕ) (a b : grPiece R I n) :
    grOf R I n (a + b) = grOf R I n a + grOf R I n b :=
  map_add (DirectSum.of (grPiece R I) n) a b

#print axioms grOf_add

/-- `grOf` is injective.
-/
theorem grOf_injective (n : ℕ) : Function.Injective (grOf R I n) := by
  intro a b h
  exact DirectSum.of_injective n h

#print axioms grOf_injective

/-- `grOf` of the graded unit is `1`.
-/
theorem grOf_one : grOf R I 0 GradedMonoid.GOne.one = 1 :=
  (DirectSum.one_def (grPiece R I)).symm

#print axioms grOf_one

/-- Component of a homogeneous element at its own degree.
-/
theorem grCoeff_of (n : ℕ) (a : grPiece R I n) :
    grCoeff R I (grOf R I n a) n = a :=
  DirectSum.of_eq_same n a

#print axioms grCoeff_of

/-- Component of a homogeneous element away from its degree.
-/
theorem grCoeff_of_ne (m n : ℕ) (a : grPiece R I m) (h : n ≠ m) :
    grCoeff R I (grOf R I m a) n = 0 :=
  DirectSum.of_eq_of_ne m n a h

#print axioms grCoeff_of_ne

/-- Component of `0`.
-/
theorem grCoeff_zero (n : ℕ) : grCoeff R I 0 n = 0 :=
  DirectSum.zero_apply n

#print axioms grCoeff_zero

/-- Component of a sum.
-/
theorem grCoeff_add (x y : associatedGraded R I) (n : ℕ) :
    grCoeff R I (x + y) n = grCoeff R I x n + grCoeff R I y n :=
  DirectSum.add_apply x y n

#print axioms grCoeff_add

/-- The degree-0 component of `1` is the graded unit.
-/
theorem grCoeff_one : grCoeff R I 1 0 = GradedMonoid.GOne.one := by
  have h1 : (1 : associatedGraded R I) =
      grOf R I 0 GradedMonoid.GOne.one := grOf_one R I |>.symm
  rw [h1]
  exact grCoeff_of R I 0 _

#print axioms grCoeff_one

/-- Every `gr` element is the finite sum of its homogeneous components.
The `Decidable` hypothesis is Mathlib's standard `DirectSum` idiom
(`DirectSum.sum_support_of`), discharged by `classical` at each use.
-/
theorem gr_sum_support (x : associatedGraded R I)
    [∀ (i : ℕ) (a : grPiece R I i), Decidable (a ≠ 0)] :
    (∑ i ∈ (toDirectSum R I x).support,
      grOf R I i (grCoeff R I x i)) = x :=
  DirectSum.sum_support_of (toDirectSum R I x)

#print axioms gr_sum_support

/-- `grRegular Q` is nontrivial: the graded unit embeds injectively via
`grOf`.
-/
instance grRegular_nontrivial {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Nontrivial (grRegular Q) := by
  have h1 : (GradedMonoid.GOne.one :
      grPiece (Localization.AtPrime Q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) 0) ≠ 0 :=
    grPiece_gOne_ne_zero _ _
  have hne : grOf (Localization.AtPrime Q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) 0
        GradedMonoid.GOne.one ≠ 0 := by
    intro h
    apply h1
    have h2 : grOf (Localization.AtPrime Q)
            (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) 0
            GradedMonoid.GOne.one =
          grOf (Localization.AtPrime Q)
            (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) 0 0 := by
      rw [grOf_zero]
      exact h
    exact grOf_injective _ _ 0 h2
  exact ⟨grOf (Localization.AtPrime Q)
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) 0
    GradedMonoid.GOne.one, 0, hne⟩

#print axioms grRegular_nontrivial

/-- Homogeneous elements of degree `≥ N`, as a set. -/
def grHomSet (N : ℕ) : Set (associatedGraded R I) :=
  {y | ∃ m z, N ≤ m ∧ grOf R I m z = y}

/-- The irrelevant ideal: the span of the positive-degree homogeneous
elements.

Specification (definition). -/
def grPlus : Ideal (associatedGraded R I) :=
  Ideal.span (grHomSet R I 1)

/-- Positive-degree homogeneous elements lie in `grPlus`.
-/
theorem grPlus_mem_of (n : ℕ) (a : grPiece R I n) (hn : 1 ≤ n) :
    grOf R I n a ∈ grPlus R I :=
  Submodule.subset_span ⟨n, a, hn, rfl⟩

#print axioms grPlus_mem_of

/-- Key graded-ring computation: the degree-0 part of a product vanishes
when the right factor has no degree-0 part. Both factors are expanded
as finite sums of homogeneous elements (`gr_sum_support`); every
summand `grOf i * grOf j = grOf (i + j)` either has positive degree
(hence vanishing degree-0 part) or is the `(0, 0)`-term, which vanishes
by the hypothesis.
-/
theorem gr_mul_coeff_zero_of_right (c y : associatedGraded R I)
    (hy : grCoeff R I y 0 = 0) : grCoeff R I (c * y) 0 = 0 := by
  classical
  let eval0Hom : associatedGraded R I →+ grPiece R I 0 :=
    { toFun := fun y => grCoeff R I y 0
      map_zero' := grCoeff_zero R I 0
      map_add' := fun x y => grCoeff_add R I x y 0 }
  have eval0_sum : ∀ (s : Finset ℕ) (f : ℕ → associatedGraded R I),
      grCoeff R I (∑ i ∈ s, f i) 0 = ∑ i ∈ s, grCoeff R I (f i) 0 :=
    fun s f => map_sum eval0Hom f s
  rw [← gr_sum_support R I c, ← gr_sum_support R I y]
  -- Term-mode: `rw [Finset.sum_mul]` fails to match since the goal's `*`
  -- instance (from our `CommRing`) differs syntactically from the lemma's.
  have hexpand : ((∑ i ∈ (toDirectSum R I c).support,
          grOf R I i (grCoeff R I c i)) *
        (∑ j ∈ (toDirectSum R I y).support,
          grOf R I j (grCoeff R I y j))) =
        ∑ i ∈ (toDirectSum R I c).support,
          ∑ j ∈ (toDirectSum R I y).support,
            (grOf R I i (grCoeff R I c i) *
              grOf R I j (grCoeff R I y j)) :=
    Finset.sum_mul_sum _ _ _ _
  rw [hexpand, eval0_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval0_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [grOf_mul]
  by_cases h : i + j = 0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h
    rw [hy]
    have hmul : GradedMonoid.GMul.mul (A := grPiece R I)
        (grCoeff R I c 0) (0 : grPiece R I 0) = 0 := by
      rw [grMul_def]
      exact map_zero _
    rw [hmul]
    have hof0 : grOf R I (0 + 0) (0 : grPiece R I (0 + 0)) = 0 :=
      grOf_zero R I _
    rw [hof0]
    exact grCoeff_zero R I 0
  · exact grCoeff_of_ne R I _ _ _ (Ne.symm h)

#print axioms gr_mul_coeff_zero_of_right

/-- Every element of `grPlus` has vanishing degree-0 component (span
induction; the smul case is the key computation above).
-/
theorem grPlus_coeff_zero_eq_zero (y : associatedGraded R I)
    (hy : y ∈ grPlus R I) : grCoeff R I y 0 = 0 := by
  refine Submodule.span_induction
    (p := fun y _ => grCoeff R I y 0 = 0) ?_ ?_ ?_ ?_ hy
  · intro x hx
    obtain ⟨m, z, hm, rfl⟩ := hx
    exact grCoeff_of_ne R I _ _ _ (by omega : (0 : ℕ) ≠ m)
  · exact grCoeff_zero R I 0
  · intro x1 x2 _ _ h1 h2
    rw [grCoeff_add, h1, h2, add_zero]
  · intro c x _ hx
    rw [smul_eq_mul]
    exact gr_mul_coeff_zero_of_right R I c x hx

#print axioms grPlus_coeff_zero_eq_zero

/-- A degree-0 homogeneous element of `grPlus` is zero.
-/
theorem grPlus_of_zero_mem {a : grPiece R I 0}
    (h : grOf R I 0 a ∈ grPlus R I) : a = 0 := by
  have h0 := grPlus_coeff_zero_eq_zero R I _ h
  rwa [grCoeff_of] at h0

#print axioms grPlus_of_zero_mem

/-- `grPlus` is proper: `1` has nonzero degree-0 part.
-/
theorem grPlus_ne_top [Nontrivial (R ⧸ I)] : grPlus R I ≠ ⊤ := by
  intro htop
  have hmem : (1 : associatedGraded R I) ∈ grPlus R I := by
    rw [htop]
    exact Submodule.mem_top
  have h0 := grPlus_coeff_zero_eq_zero R I 1 hmem
  rw [grCoeff_one] at h0
  exact grPiece_gOne_ne_zero R I h0

#print axioms grPlus_ne_top

/-! ## §2. The filtration link (forward): `grPlus^N = ⊥ → dim R_Q = 0` -/

/-- Every degree-`N` class lifts into `grPlus^N`: span induction on
`𝔪^{1+N} = 𝔪 * 𝔪^N` (generalizing `grPiece_span_mul_eq_top`), with the
scalar case via the `R`-scalar-as-`gr`-product identity.
-/
theorem gr_of_mem_grPlus_pow (N : ℕ) (x : R) (hx : x ∈ I ^ N) :
    grOf R I N (Submodule.Quotient.mk (⟨x, hx⟩ : ↥(I ^ N))) ∈
      grPlus R I ^ N := by
  revert x hx
  induction N with
  | zero =>
    intro x hx
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ N IH =>
    intro x
    rw [show N + 1 = 1 + N from add_comm _ _]
    intro hx
    have hmem : x ∈ Submodule.span R
        (((I ^ 1 : Ideal R) : Set R) * ((I ^ N : Ideal R) : Set R)) := by
      have hr : x ∈ I ^ 1 * I ^ N := by
        rw [← pow_add]
        exact hx
      rwa [Submodule.mul_eq_span_mul_set] at hr
    have hle : Submodule.span R
          (((I ^ 1 : Ideal R) : Set R) * ((I ^ N : Ideal R) : Set R)) ≤
        I ^ (1 + N) := by
      rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_mul] at hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [pow_add]
      exact Ideal.mul_mem_mul ha hb
    have main : ∀ (y : R)
        (hy : y ∈ Submodule.span R (((I ^ 1 : Ideal R) : Set R) *
          ((I ^ N : Ideal R) : Set R))),
        grOf R I (1 + N) (Submodule.Quotient.mk
          (⟨y, hle hy⟩ : ↥(I ^ (1 + N)))) ∈ grPlus R I ^ (1 + N) := by
      intro y hy
      refine Submodule.span_induction
        (p := fun y hy => grOf R I (1 + N) (Submodule.Quotient.mk
          (⟨y, hle hy⟩ : ↥(I ^ (1 + N)))) ∈ grPlus R I ^ (1 + N))
        ?_ ?_ ?_ ?_ hy
      · intro y hy
        rw [Set.mem_mul] at hy
        obtain ⟨a, ha, b, hb, rfl⟩ := hy
        have hmul_eq : grOf R I (1 + N) (Submodule.Quotient.mk
                (⟨a * b, hle (Submodule.subset_span hy)⟩ :
                  ↥(I ^ (1 + N)))) =
            (grOf R I 1 (Submodule.Quotient.mk
              (⟨a, ha⟩ : ↥(I ^ 1)))) *
              (grOf R I N (Submodule.Quotient.mk
                (⟨b, hb⟩ : ↥(I ^ N)))) := by
          rw [grOf_mul]
          -- `congr 1` closes this: the components agree definitionally
          -- (`GMul.mul` of classes reduces to the class of the product).
          congr 1
        have hcomm : (grOf R I 1 (Submodule.Quotient.mk
                (⟨a, ha⟩ : ↥(I ^ 1)))) *
              (grOf R I N (Submodule.Quotient.mk
                (⟨b, hb⟩ : ↥(I ^ N)))) =
            (grOf R I N (Submodule.Quotient.mk
              (⟨b, hb⟩ : ↥(I ^ N)))) *
              (grOf R I 1 (Submodule.Quotient.mk
                (⟨a, ha⟩ : ↥(I ^ 1)))) := mul_comm _ _
        rw [hmul_eq, hcomm, add_comm 1 N, pow_succ]
        exact Ideal.mul_mem_mul (IH b hb) (grPlus_mem_of R I 1 _ le_rfl)
      · have hmk0 : (Submodule.Quotient.mk
            (0 : ↥(I ^ (1 + N))) : grPiece R I (1 + N)) = 0 := by
          rw [← grPiece_mkQ_eq_mk]
          exact map_zero _
        have h0sub : (⟨0, hle (Submodule.zero_mem _)⟩ :
            ↥(I ^ (1 + N))) = 0 := Subtype.ext rfl
        rw [h0sub, hmk0, grOf_zero]
        exact Submodule.zero_mem _
      · intro x1 x2 hx1 hx2 ih1 ih2
        have hsub : (⟨x1 + x2, hle (Submodule.add_mem _ hx1 hx2)⟩ :
            ↥(I ^ (1 + N))) =
            (⟨x1, hle hx1⟩ + ⟨x2, hle hx2⟩) := Subtype.ext rfl
        rw [hsub, ← grPiece_mk_add, grOf_add]
        exact Submodule.add_mem _ ih1 ih2
      · intro c x hx ih
        have hsub : (⟨c • x, hle (Submodule.smul_mem _ _ hx)⟩ :
            ↥(I ^ (1 + N))) =
            c • (⟨x, hle hx⟩ : ↥(I ^ (1 + N))) := Subtype.ext rfl
        rw [hsub, ← grPiece_mk_smul]
        have hsmul_eq : grOf R I (1 + N)
              (c • Submodule.Quotient.mk
                (⟨x, hle hx⟩ : ↥(I ^ (1 + N)))) =
            (grOf R I 0 (Submodule.Quotient.mk
              (⟨c, by simp⟩ : ↥(I ^ 0)))) *
              (grOf R I (1 + N) (Submodule.Quotient.mk
                (⟨x, hle hx⟩ : ↥(I ^ (1 + N))))) := by
          -- Swap first: `grOf_mul` then yields the *definitional* index
          -- `(1 + N) + 0`, avoiding a `zero_add` dependent rewrite.
          have hcomm0 : (grOf R I 0 (Submodule.Quotient.mk
                  (⟨c, by simp⟩ : ↥(I ^ 0)))) *
                (grOf R I (1 + N) (Submodule.Quotient.mk
                  (⟨x, hle hx⟩ : ↥(I ^ (1 + N))))) =
                (grOf R I (1 + N) (Submodule.Quotient.mk
                  (⟨x, hle hx⟩ : ↥(I ^ (1 + N))))) *
                (grOf R I 0 (Submodule.Quotient.mk
                  (⟨c, by simp⟩ : ↥(I ^ 0)))) :=
            mul_comm _ _
          rw [hcomm0, grOf_mul]
          congr 1
          rw [grMul_mk_mk, grPiece_mk_smul]
          congr 1
          refine Subtype.ext ?_
          rw [grMulRep_apply]
          exact (smul_eq_mul _ _).trans (mul_comm _ _)
        rw [hsmul_eq, ← smul_eq_mul]
        exact Submodule.smul_mem _ _ ih
    have hsubeq : (⟨x, hle hmem⟩ : ↥(I ^ (1 + N))) = ⟨x, hx⟩ :=
      Subtype.ext rfl
    rw [← hsubeq]
    exact main x hmem

#print axioms gr_of_mem_grPlus_pow

/-- The filtration link: `grPlus^N = ⊥` forces `𝔪^N ≤ 𝔪^{N+1}`
(the degree-`N` class of `x ∈ 𝔪^N` lies in `grPlus^N`, hence
vanishes).
-/
theorem pow_le_succ_of_grPlus_pow_eq_bot {N : ℕ}
    (h : grPlus R I ^ N = ⊥) : I ^ N ≤ I ^ (N + 1) := by
  intro x hx
  have hmem := gr_of_mem_grPlus_pow R I N x hx
  rw [h] at hmem
  have h0 : grOf R I N
      (Submodule.Quotient.mk (⟨x, hx⟩ : ↥(I ^ N))) = 0 :=
    (Submodule.mem_bot _).mp hmem
  have hmk0 : (Submodule.Quotient.mk (⟨x, hx⟩ : ↥(I ^ N)) :
      grPiece R I N) = 0 := by
    apply grOf_injective R I N
    rw [grOf_zero]
    exact h0
  exact (grPiece_mk_eq_zero_iff R I N _).mp hmk0

#print axioms pow_le_succ_of_grPlus_pow_eq_bot

/-- R-side collapse assembly: `grPlus^N = ⊥` forces `dim R_Q = 0`
(reuses the GatedDischarge Nakayama collapse).
-/
theorem dim_atPrime_eq_zero_of_grPlus_pow_eq_bot {K : Type*} [Field K]
    {m : ℕ} (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] {N : ℕ}
    (h : grPlus (Localization.AtPrime Q)
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N = ⊥) :
    ringKrullDim (Localization.AtPrime Q) = 0 :=
  GatedDischarge.dim_atPrime_eq_zero_of_pow_le_succ Q N
    (pow_le_succ_of_grPlus_pow_eq_bot _ _ h)

#print axioms dim_atPrime_eq_zero_of_grPlus_pow_eq_bot

/-- At embdim 2, no power of `grPlus` vanishes (`dim R_Q = 2 ≠ 0`).
-/
theorem grPlus_pow_ne_bot_of_embdim_two {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hemb : 2 = (IsLocalRing.maximalIdeal
      (Localization.AtPrime Q)).spanFinrank) (N : ℕ) :
    grPlus (Localization.AtPrime Q)
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N ≠ ⊥ := by
  intro h
  have hdim := dim_atPrime_eq_zero_of_grPlus_pow_eq_bot Q h
  have h2 := SystemOfParametersWiring.sop_consume_dim_atPrime_eq_two Q hemb
  exact absurd (hdim.symm.trans h2) (by decide)

#print axioms grPlus_pow_ne_bot_of_embdim_two

/-! ## §3. Reverse + Artinian collapse: `dim R_Q = 0 ⟺ ∃ N, grPlus^N = ⊥` -/

/-- `grPlus^N` is spanned by homogeneous elements of degree `≥ N`
(induction via `span_mul_span`: degrees add under multiplication).
-/
theorem grPlus_pow_le_span_ge (N : ℕ) :
    grPlus R I ^ N ≤ Ideal.span (grHomSet R I N) := by
  induction N with
  | zero =>
    rw [pow_zero]
    intro y _
    classical
    rw [← gr_sum_support R I y]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨i, grCoeff R I y i, Nat.zero_le i, rfl⟩
  | succ N IH =>
    rw [pow_succ]
    have hmul : grPlus R I ^ N * grPlus R I ≤
        Ideal.span (grHomSet R I N) * Ideal.span (grHomSet R I 1) :=
      Ideal.mul_mono IH le_rfl
    rw [Ideal.span_mul_span] at hmul
    refine hmul.trans ?_
    rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_mul] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨m, u, hm, rfl⟩ := ha
    obtain ⟨k, v, hk, rfl⟩ := hb
    rw [grOf_mul]
    apply Submodule.subset_span
    exact ⟨m + k, _, by omega, rfl⟩

#print axioms grPlus_pow_le_span_ge

/-- A nilpotent maximal-ideal power kills the corresponding `grPlus`
power: every generator has degree `≥ N`, where the graded piece
vanishes.
-/
theorem grPlus_pow_eq_bot_of_pow_maximalIdeal_eq_bot {N : ℕ}
    (h : I ^ N = ⊥) : grPlus R I ^ N = ⊥ := by
  have hle := grPlus_pow_le_span_ge R I N
  refine eq_bot_iff.mpr (hle.trans ?_)
  rw [Submodule.span_le]
  intro y hy
  obtain ⟨m, z, hm, rfl⟩ := hy
  have hpow : I ^ m = ⊥ := by
    have hle2 : I ^ m ≤ I ^ N := Ideal.pow_le_pow_right hm
    rw [h] at hle2
    exact eq_bot_iff.mpr hle2
  have hz : z = 0 := by
    obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I m z
    have hr0 : (r : R) = 0 := by
      have hmem : (r : R) ∈ (⊥ : Ideal R) := by
        rw [← hpow]
        exact r.2
      exact (Submodule.mem_bot _).mp hmem
    have hrsub : r = 0 := Subtype.ext hr0
    rw [hrsub]
    rw [← grPiece_mkQ_eq_mk]
    exact map_zero _
  rw [hz, grOf_zero]
  exact Submodule.zero_mem _

#print axioms grPlus_pow_eq_bot_of_pow_maximalIdeal_eq_bot

/-- Artinian-collapse reuse: `dim R_Q = 0` gives a vanishing `grPlus`
power (Hopkins–Levitzki makes `R_Q` Artinian, the maximal ideal goes
nilpotent, §3-reverse applies).
-/
theorem grPlus_pow_eq_bot_of_dim_eq_zero {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (h : ringKrullDim (Localization.AtPrime Q) = 0) :
    ∃ N, grPlus (Localization.AtPrime Q)
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N = ⊥ := by
  have hkle : Ring.KrullDimLE 0 (Localization.AtPrime Q) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr h
  have hart : IsArtinianRing (Localization.AtPrime Q) :=
    isArtinianRing_iff_krullDimLE_zero.mpr hkle
  have hnil : IsNilpotent
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal _).mp hart
  obtain ⟨N, hN⟩ := hnil
  refine ⟨N, grPlus_pow_eq_bot_of_pow_maximalIdeal_eq_bot _ _ ?_⟩
  rw [hN]
  exact Ideal.zero_eq_bot

#print axioms grPlus_pow_eq_bot_of_dim_eq_zero

/-- The irrelevant ideal is nilpotent iff `dim R_Q = 0`.
-/
theorem grPlus_pow_eq_bot_iff_dim_eq_zero {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    (∃ N, grPlus (Localization.AtPrime Q)
        (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) ^ N = ⊥) ↔
      ringKrullDim (Localization.AtPrime Q) = 0 := by
  constructor
  · rintro ⟨N, hN⟩
    exact dim_atPrime_eq_zero_of_grPlus_pow_eq_bot Q hN
  · exact grPlus_pow_eq_bot_of_dim_eq_zero Q

#print axioms grPlus_pow_eq_bot_iff_dim_eq_zero

/-! ## §4. Graded Nakayama factored through Mathlib Nakayama -/

/-- Graded Nakayama, Mathlib side closed: a finitely generated submodule
absorbed by `grPlus` is `⊥`, conditional on `grPlus` lying in the
Jacobson radical. The hypothesis is exactly where homogeneous data
enters (gap-gn-1, §6) — it is false ungraded in general.

Conditional on exactly `[grPlus ≤ jacobson ⊥]`. -/
theorem graded_nakayama_of_le_jacobson {M : Type*} [AddCommGroup M]
    [Module (associatedGraded R I) M]
    (hle : grPlus R I ≤ Ideal.jacobson ⊥)
    (N : Submodule (associatedGraded R I) M) (hN : N.FG)
    (hsub : N ≤ grPlus R I • N) : N = ⊥ := by
  obtain ⟨r, hr, hr'⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      (grPlus R I) N hN hsub
  have hunit : IsUnit r := by
    by_contra hnu
    have hspan_ne : Ideal.span ({r} : Set (associatedGraded R I)) ≠ ⊤ := by
      intro htop
      have h1mem : (1 : associatedGraded R I) ∈
          Ideal.span ({r} : Set (associatedGraded R I)) :=
        (Ideal.eq_top_iff_one _).mp htop
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1mem
      exact hnu ⟨⟨r, a, by rw [mul_comm]; exact ha, ha⟩, rfl⟩
    obtain ⟨Mx, hM, hleM⟩ := Ideal.exists_le_maximal _ hspan_ne
    have hrM : r ∈ Mx := hleM (Ideal.mem_span_singleton_self r)
    have hjacM : Ideal.jacobson (⊥ : Ideal (associatedGraded R I)) ≤ Mx :=
      sInf_le ⟨bot_le, hM⟩
    have hr1M : r - 1 ∈ Mx := hjacM (hle hr)
    have h1M : (1 : associatedGraded R I) ∈ Mx := by
      have h := Mx.add_mem hrM (Mx.neg_mem hr1M)
      have heq : r + -(r - 1) = (1 : associatedGraded R I) := by
        rw [← sub_eq_add_neg, sub_sub_cancel]
      rw [heq] at h
      exact h
    exact hM.ne_top ((Ideal.eq_top_iff_one Mx).mpr h1M)
  rw [Submodule.eq_bot_iff]
  intro n hn
  have h0 : r • n = 0 := hr' n hn
  obtain ⟨u, hu⟩ := hunit
  have h0' : ((u : (associatedGraded R I)ˣ) : associatedGraded R I) • n =
      0 := by
    rw [hu]
    exact h0
  have h1 : (((u⁻¹ : (associatedGraded R I)ˣ)) : associatedGraded R I) *
      (((u : (associatedGraded R I)ˣ)) : associatedGraded R I) = 1 :=
    u.inv_mul
  calc n = (1 : associatedGraded R I) • n := (one_smul _ _).symm
    _ = (((u⁻¹ : (associatedGraded R I)ˣ) : associatedGraded R I) *
        (((u : (associatedGraded R I)ˣ)) : associatedGraded R I)) • n := by
          rw [h1]
    _ = (((u⁻¹ : (associatedGraded R I)ˣ)) : associatedGraded R I) •
        ((((u : (associatedGraded R I)ˣ)) : associatedGraded R I) • n) :=
          mul_smul _ _ _
    _ = 0 := by rw [h0', smul_zero]

#print axioms graded_nakayama_of_le_jacobson

/-! ## §5. Homogeneous attack: avoidance SPECs + dimension masters -/

/-- Homogeneous ideal: closed under taking homogeneous components.
Self-contained component definition (Mathlib's `GradedRing`
decomposition API does not apply to `associatedGraded` directly).

Specification (definition). -/
def IsHomogeneousIdeal (P : Ideal (associatedGraded R I)) : Prop :=
  ∀ y ∈ P, ∀ n, grOf R I n (grCoeff R I y n) ∈ P

/-- `grPlus` is homogeneous: the degree-0 component of a `grPlus`
element vanishes (§1), and positive-degree components are generators.
-/
theorem grPlus_isHomogeneous : IsHomogeneousIdeal R I (grPlus R I) := by
  intro y hy n
  by_cases hn : n = 0
  · subst hn
    have h0 : grCoeff R I y 0 = 0 :=
      grPlus_coeff_zero_eq_zero R I y hy
    rw [h0, grOf_zero]
    exact Submodule.zero_mem _
  · exact grPlus_mem_of R I n _ (Nat.one_le_iff_ne_zero.mpr hn)

#print axioms grPlus_isHomogeneous

/-- Homogeneous prime: prime + homogeneous.

Specification (definition). -/
def IsHomogeneousPrime (P : Ideal (associatedGraded R I)) : Prop :=
  P.IsPrime ∧ IsHomogeneousIdeal R I P

/-- Homogeneous-component extraction: a `grPlus` element outside `P`
yields a homogeneous `grPlus` element outside `P` (else the finite
homogeneous decomposition would put it in `P`).
-/
theorem homogeneous_of_mem_grPlus_not_mem
    {P : Ideal (associatedGraded R I)}
    {x : associatedGraded R I} (hx : x ∈ grPlus R I) (hxP : x ∉ P) :
    ∃ h, h ∈ grPlus R I ∧ h ∉ P ∧
      ∃ j a, grOf R I j a = h := by
  classical
  by_cases h : ∀ i ∈ (toDirectSum R I x).support,
    grOf R I i (grCoeff R I x i) ∈ P
  · exfalso
    apply hxP
    rw [← gr_sum_support R I x]
    exact Submodule.sum_mem _ fun i hi => h i hi
  · push Not at h
    obtain ⟨i, hi, hPi⟩ := h
    exact ⟨_, grPlus_isHomogeneous R I x hx i, hPi, i, _, rfl⟩

#print axioms homogeneous_of_mem_grPlus_not_mem

/-- Homogeneous properness: adjoining a positive-degree homogeneous
element outside a homogeneous prime stays proper. Reading the relation
`1 = p + c * h` in degree 0: `c * h` has no degree-0 part (the §1 key
computation), and `p`'s degree-0 part lies in `P` (homogeneity),
forcing `1 ∈ P`.
-/
theorem sup_span_singleton_ne_top_of_homogeneous
    {P : Ideal (associatedGraded R I)} (hP : IsHomogeneousPrime R I P)
    {j : ℕ} {a : grPiece R I j} (hj : 1 ≤ j)
    -- `h ∉ P` is unused: the degree-0 reading forces `1 ∈ P` regardless.
    (_hPi : grOf R I j a ∉ P) :
    P ⊔ Ideal.span ({grOf R I j a} :
      Set (associatedGraded R I)) ≠ ⊤ := by
  obtain ⟨hprime, hhom⟩ := hP
  intro htop
  have h1mem : (1 : associatedGraded R I) ∈ P ⊔
      Ideal.span ({grOf R I j a} :
        Set (associatedGraded R I)) :=
    (Ideal.eq_top_iff_one _).mp htop
  obtain ⟨p, hpP, z, hz, hpz⟩ := Submodule.mem_sup.mp h1mem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
  have hdeg : (grCoeff R I p 0) + (grCoeff R I (c * grOf R I j a) 0) =
      GradedMonoid.GOne.one := by
    have hcon : grCoeff R I (p + z) 0 = grCoeff R I 1 0 := by
      rw [hpz]
    rw [grCoeff_add, ← hc, grCoeff_one] at hcon
    exact hcon
  have hvan : (grCoeff R I (c * grOf R I j a) 0) = 0 := by
    apply gr_mul_coeff_zero_of_right
    exact grCoeff_of_ne R I _ _ _ (by omega : (0 : ℕ) ≠ j)
  rw [hvan, add_zero] at hdeg
  have hp0P : grOf R I 0 (grCoeff R I p 0) ∈ P := hhom p hpP 0
  rw [hdeg, grOf_one] at hp0P
  exact hprime.ne_top ((Ideal.eq_top_iff_one P).mpr hp0P)

#print axioms sup_span_singleton_ne_top_of_homogeneous

/-- A homogeneous prime missing `grPlus` sits strictly below a maximal
ideal (homogeneous extraction + positive degree + properness + Krull).
-/
theorem exists_maximal_sup_of_homogeneousAvoid
    {P : Ideal (associatedGraded R I)} (hP : IsHomogeneousPrime R I P)
    (havoid : ¬ grPlus R I ≤ P) :
    ∃ M : Ideal (associatedGraded R I), M.IsMaximal ∧ P < M := by
  obtain ⟨hprime, hhom⟩ := hP
  have hex : ∃ x, x ∈ grPlus R I ∧ x ∉ P := by
    by_contra hall
    push Not at hall
    exact havoid hall
  obtain ⟨x, hx, hxP⟩ := hex
  obtain ⟨hh, hhmem, hhP, j, a, rfl⟩ :=
    homogeneous_of_mem_grPlus_not_mem R I hx hxP
  have hj : 1 ≤ j := by
    by_contra hlt
    push Not at hlt
    have hj0 : j = 0 := Nat.lt_one_iff.mp hlt
    subst hj0
    have ha0 : a = 0 := grPlus_of_zero_mem R I hhmem
    rw [ha0] at hhP
    have hof0 : grOf R I 0 (0 : grPiece R I 0) = 0 := grOf_zero R I _
    rw [hof0] at hhP
    exact hhP (Submodule.zero_mem _)
  have hproper : P ⊔ Ideal.span ({grOf R I j a} :
      Set (associatedGraded R I)) ≠ ⊤ :=
    sup_span_singleton_ne_top_of_homogeneous R I ⟨hprime, hhom⟩ hj hhP
  obtain ⟨M, hMmax, hleM⟩ := Ideal.exists_le_maximal _ hproper
  have hmemM : grOf R I j a ∈ M :=
    hleM (Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _,
      grOf R I j a, Ideal.mem_span_singleton_self _,
      zero_add _⟩)
  refine ⟨M, hMmax, lt_of_le_of_ne (le_sup_left.trans hleM) ?_⟩
  intro heq
  apply hhP
  rw [heq]
  exact hmemM

#print axioms exists_maximal_sup_of_homogeneousAvoid

/-- Order lift for `WithBot ℕ∞`: past `n` means at least `n + 1`.
-/
theorem withbot_succ_le_of_not_le {n : ℕ} {d : WithBot ℕ∞}
    (h : ¬ d ≤ ((n : ℕ) : WithBot ℕ∞)) :
    (((n + 1 : ℕ)) : WithBot ℕ∞) ≤ d := by
  have hlt : ((n : ℕ) : WithBot ℕ∞) < d := lt_of_not_ge h
  have hle := ENat.WithBot.add_one_le_iff.mpr hlt
  simpa using hle

#print axioms withbot_succ_le_of_not_le

/-- Order corollary: past `0` means at least `1`.
-/
theorem withbot_one_le_of_not_le_zero {d : WithBot ℕ∞}
    (h : ¬ d ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ d := by
  have h1 := withbot_succ_le_of_not_le (n := 0) h
  simpa using h1

#print axioms withbot_one_le_of_not_le_zero

/-- Order corollary: past `1` means at least `2`.
-/
theorem withbot_two_le_of_not_le_one {d : WithBot ℕ∞}
    (h : ¬ d ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ((2 : ℕ) : WithBot ℕ∞) ≤ d := by
  have h2 := withbot_succ_le_of_not_le (n := 1) h
  simpa using h2

#print axioms withbot_two_le_of_not_le_one

/-- Per-prime homogeneous avoidance: some homogeneous prime misses
`grPlus`.

Specification (Prop address for the homogeneous remainder). -/
def HhomogeneousAvoidAtPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] : Prop :=
  ∃ P : Ideal (grRegular Q), IsHomogeneousPrime _ _ P ∧ ¬ grPlus _ _ ≤ P

/-- Per-prime homogeneous non-minimal avoidance: some non-minimal
homogeneous prime misses `grPlus`.

Specification (Prop address for the narrow remainder). -/
def HhomogeneousNonminAvoidAtPrime {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] : Prop :=
  ∃ P : Ideal (grRegular Q), IsHomogeneousPrime _ _ P ∧
    P ∉ minimalPrimes (grRegular Q) ∧ ¬ grPlus _ _ ≤ P

/-- Ass-level narrow remainder at embdim 2 (mirrors GT's
`GrDimGe2D2AtAss` binder shape).

Specification (Prop address for the narrow remainder). -/
def HhomogeneousNonminAvoidD2AtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
      ∀ _hemb : 2 = (IsLocalRing.maximalIdeal
        (Localization.AtPrime Q)).spanFinrank,
        HhomogeneousNonminAvoidAtPrime Q

/-- `1 ≤ dim gr` from homogeneous avoidance (the `0`-slice discharge in
homogeneous form; needs no upper-bound input).

Conditional on exactly `[h]`. -/
theorem grDimGe1_of_homogeneousAvoid {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (h : HhomogeneousAvoidAtPrime Q) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (grRegular Q) := by
  obtain ⟨P, hP, havoid⟩ := h
  obtain ⟨hprime, hhom⟩ := hP
  obtain ⟨M, hMmax, hpltM⟩ :=
    exists_maximal_sup_of_homogeneousAvoid _ _ ⟨hprime, hhom⟩ havoid
  have hPnotmax : ¬ P.IsMaximal := by
    intro hmax
    have heq := hmax.eq_of_le hMmax.ne_top (le_of_lt hpltM)
    exact (ne_of_lt hpltM) heq
  have hkle0 : ¬ Ring.KrullDimLE 0 (grRegular Q) := by
    rw [Ring.krullDimLE_zero_iff]
    push Not
    exact ⟨P, hprime, hPnotmax⟩
  have hle0 : ¬ ringKrullDim (grRegular Q) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast fun hh =>
      hkle0 ((Ring.krullDimLE_iff (R := grRegular Q) (n := 0)).mpr hh)
  have h1 := withbot_one_le_of_not_le_zero hle0
  exact_mod_cast h1

#print axioms grDimGe1_of_homogeneousAvoid

/-- `2 ≤ dim gr` from homogeneous non-minimal avoidance: the prime is
neither minimal (SPEC) nor maximal (helper chain), so `¬ KrullDimLE 1`.

Conditional on exactly `[h]`. -/
theorem grDimGe2_of_homogeneousNonminAvoid {K : Type*} [Field K] {m : ℕ}
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (h : HhomogeneousNonminAvoidAtPrime Q) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (grRegular Q) := by
  obtain ⟨P, hP, hPnonmin, havoid⟩ := h
  obtain ⟨hprime, hhom⟩ := hP
  obtain ⟨M, hMmax, hpltM⟩ :=
    exists_maximal_sup_of_homogeneousAvoid _ _ ⟨hprime, hhom⟩ havoid
  have hPnotmax : ¬ P.IsMaximal := by
    intro hmax
    have heq := hmax.eq_of_le hMmax.ne_top (le_of_lt hpltM)
    exact (ne_of_lt hpltM) heq
  have hkle1 : ¬ Ring.KrullDimLE 1 (grRegular Q) := by
    rw [Ring.krullDimLE_one_iff]
    push Not
    exact ⟨P, hprime, hPnonmin, hPnotmax⟩
  have hle1 : ¬ ringKrullDim (grRegular Q) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast fun hh =>
      hkle1 ((Ring.krullDimLE_iff (R := grRegular Q) (n := 1)).mpr hh)
  have h2 := withbot_two_le_of_not_le_one hle1
  exact_mod_cast h2

#print axioms grDimGe2_of_homogeneousNonminAvoid

/-- Ass-level attack master: GT's `GrDimGe2D2AtAss` from the narrow
homogeneous-avoidance remainder.

Conditional on exactly `[h]`. -/
theorem grDimGe2D2_of_homogeneousNonminAvoid (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : HhomogeneousNonminAvoidD2AtAss m K J) :
    GatedDischarge.GrDimGe2D2AtAss m K J := by
  intro Q _ hQ hemb
  exact grDimGe2_of_homogeneousNonminAvoid Q (h Q hQ hemb)

#print axioms grDimGe2D2_of_homogeneousNonminAvoid

/-- Downstream: `HkerD2AtAss` from the narrow remainder (via GT's §1
ring joint).

Conditional on exactly `[h]`. -/
theorem hkerD2_of_homogeneousNonminAvoid (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (h : HhomogeneousNonminAvoidD2AtAss m K J) :
    WitnessKernelDimTwo.HkerD2AtAss m K J :=
  (GatedDischarge.grDimGe2_iff_hkerD2 m K J).mp
    (grDimGe2D2_of_homogeneousNonminAvoid m K J h)

#print axioms hkerD2_of_homogeneousNonminAvoid

/-! ## §6. Gap-gn register + residual register (doc-only)

scoped homogeneous items (none attempted beyond the factoring in §4;
all need homogeneous-ideal machinery absent from Mathlib v4.34.0):

* Gap-gn-1 (graded Nakayama proper): `grPlus ≤ jacobson ⊥` from
  homogeneous data, i.e. every element of `grPlus` lies in every maximal
  ideal — equivalently the homogeneous-maximal-ideal theory (existence
  of maximal homogeneous ideals, graded fields concentrated in
  degree 0). Needed to fire §4 toward `grPlus^N = ⊥` from Artinian `gr`.
  Estimate: ~200 lines (homogeneous maximal spectrum + graded-field
  lemma + Jacobson containment).
* Gap-gn-2 (homogeneous minimal primes): minimal primes over a
  homogeneous ideal can be chosen homogeneous (Zorn on homogeneous
  ideals + homogeneous union-of-chain + homogeneous Krull-type lemmas).
  Needed to produce the SPEC prime from bare existence. Estimate: ~150
  lines.
* Gap-gn-3 (avoidance discharge at embdim 2): from gap-gn-1/2, produce a
  non-minimal homogeneous prime missing `grPlus` at embdim-2 Ass primes
  (homogeneous prime avoidance at `d = 2` + a height argument that the
  avoided prime is not minimal). Estimate: ~120 lines given gap-gn-1/2.
* CM-ness of regular rings (not attempted, not scoped here): scoped as large work
  in (`HSDegree` §4); the equidimensionality route to
  `dim gr ≥ 1` unconditionally stays out of scope.

minimal non-circular remainder (verbatim):
`HhomogeneousNonminAvoidD2AtAss` — per `Q ∈ Ass(R ⧸ J)` at embdim
exactly 2, there is a non-minimal homogeneous prime missing `grPlus`.
A single structured-prime existence per prime; no dimension inequality,
no datum binders.

why the remainder is strictly narrower (all machine-checked):

* The `0`-slice is gone: §§2–3 show `grPlus^N = ⊥ ⟺ dim R_Q = 0`
  unconditionally, so at embdim 2 (`dim R_Q = 2`) every `grPlus^N ≠ ⊥`.
  (Note: `∀ N, grPlus^N ≠ ⊥` does not imply `dim gr ≥ 1` ungraded —
  `κ[t]/(t^2 - t)` is a graded counterexample with `R₀` a field,
  `grPlus^N = (t) ≠ ⊥`, `dim = 0` — so homogeneous data is genuinely
  needed, and the SPEC supplies exactly it.)
* The masters (§5) need no upper-bound input: `¬ KrullDimLE 0/1` lifts
  to `1/2 ≤ dim` by pure order theory (`withbot_*` lemmas).
* Nothing assumes `hwit`, `hmult`, `hdimEq`, `ker = ⊥`, or any growth
  fact; the only undischarged input in §5 is the narrow remainder
  itself. The ungated `HsopGrLowerD2AtAss` is never touched (refuted in
  `GatedGrLower` §3).

consumers: any future per-prime non-minimal-homogeneous-avoidance proof
at embdim 2 discharges the narrow remainder — hence GT's
`GrDimGe2D2AtAss` and (via the §1 ring joint) every `d = 2` form — by a
single `exact`.
-/

end GradedNakayamaBank
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
