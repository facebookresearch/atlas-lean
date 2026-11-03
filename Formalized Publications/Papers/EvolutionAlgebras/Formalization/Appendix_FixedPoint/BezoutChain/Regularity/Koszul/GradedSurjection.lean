/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing

/-!
# The canonical graded surjection onto `gr_I(R)` (Koszul-plan step A4, M4b)

Step M4b of the associated-graded milestone (see
`EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Regularity.Koszul.AssociatedGradedRing`,
remaining M4a–M4c):
for generators `g : Fin d → R` of an ideal `I` (as
`Ideal.span (Set.range g) = I`), the canonical graded surjection
`MvPolynomial (Fin d) (R ⧸ I) →+* associatedGraded R I`, via the polynomial
universal property (`MvPolynomial.eval₂Hom`) plus surjectivity degree by
degree from `grPiece_span_mul_eq_top`.

The coefficient map `R ⧸ I → gr` factors the degree-0 inclusion through
`Ideal.Quotient.lift` (no M4a identification needed); variables map to the
degree-1 generator classes. The per-degree surjectivity induction (§3) shows
every homogeneous element `DirectSum.of _ n x` is hit: degree 0 by constants,
degree 1 by span induction on the generators, degree `1 + n` by
`grPiece_span_mul_eq_top` (products of hit classes are hit).

## Shape for M4c-ii

M4c-ii (dim-equality forces injectivity) consumes the first-isomorphism form
`polySurj_quotKerEquiv`: the polynomial ring over the residue *field*
(`polySurjResidue_quotKerEquiv` for `grRegular P`) modulo the kernel is `gr`,
so `dim (MvPolynomial ⧸ ker) = dim gr` and equality with `dim MvPolynomial`
forces `ker = ⊥`.

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only:
* `Algebra/DirectSum/Basic.lean` + `Ring.lean`: `of`, `induction_on`,
  `of_zero_one` (multiplication goes through the project-level
  `associatedGraded_of_mul_of`).
* `Algebra/MvPolynomial/Eval.lean`: `eval₂Hom` (+ `eval₂Hom_C`, `eval₂Hom_X'`).
* `RingTheory/Ideal/Quotient/Defs.lean` + `Operations.lean`: `lift`, `mk`,
  `RingHom.quotientKerEquivOfSurjective`.

Project (read-only):
* `Regularity/Koszul/AssociatedGradedRing.lean` (steps A4(i), M4a–M4c input: `grPiece`,
  `associatedGraded`, `grPiece_span_mul_eq_top`, `grRegular`).

## Status

* `polySurj`, `polySurj_surjective`: unconditional.
* `polySurj_quotKerEquiv`: unconditional (first isomorphism theorem).
* `polySurjResidue`, `polySurjResidue_surjective`,
  `polySurjResidue_quotKerEquiv`: unconditional.
-/


namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace GradedSurjection

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AssociatedGradedRing

variable (R : Type*) [CommRing R] (I : Ideal R)

/-! ## §1. Degree-0 classes and the coefficient map -/

/-- The class of `r` in degree 0 (`I ^ 0 = ⊤`, so every `r` represents). -/
def grMk0 (r : R) : grPiece R I 0 :=
  Submodule.Quotient.mk
    (⟨r, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩ : ↥(I ^ 0))

/-- Transporting a homogeneous element along an index equation. -/
theorem of_cast_eq (n m : ℕ) (e : n = m) (z : grPiece R I n) :
    DirectSum.of (grPiece R I) n z =
      DirectSum.of (grPiece R I) m (cast (congrArg (grPiece R I) e) z) := by
  subst e
  rfl

/-- Degree-0 `of` preserves multiplication. -/
theorem of_grMk0_mul (r s : R) :
    DirectSum.of (grPiece R I) 0 (grMk0 R I (r * s)) =
      DirectSum.of (grPiece R I) 0 (grMk0 R I r) *
        DirectSum.of (grPiece R I) 0 (grMk0 R I s) := by
  have e : (0 : ℕ) = 0 + 0 := rfl
  rw [associatedGraded_of_mul_of, of_cast_eq R I 0 (0 + 0) e]
  -- `congr 1` closes by `rfl`: `e` is `rfl`, so the cast reduces.
  congr 1

/-- The degree-0 inclusion `R → gr`, `r ↦ [r]₀`, as a ring hom.
-/
def degZeroHom : R →+* associatedGraded R I where
  toFun r := DirectSum.of (grPiece R I) 0 (grMk0 R I r)
  map_one' := by
    change DirectSum.of (grPiece R I) 0 (grMk0 R I 1) = 1
    change DirectSum.of (grPiece R I) 0 (1 : grPiece R I 0) = 1
    exact DirectSum.of_zero_one _
  map_mul' := fun r s => by
    change DirectSum.of (grPiece R I) 0 (grMk0 R I (r * s)) =
      DirectSum.of (grPiece R I) 0 (grMk0 R I r) *
        DirectSum.of (grPiece R I) 0 (grMk0 R I s)
    exact of_grMk0_mul R I r s
  map_zero' := by
    change DirectSum.of (grPiece R I) 0 (grMk0 R I 0) = 0
    rw [← map_zero (DirectSum.of (grPiece R I) 0)]
    congr 1
  map_add' := fun r s => by
    change DirectSum.of (grPiece R I) 0 (grMk0 R I (r + s)) =
      DirectSum.of (grPiece R I) 0 (grMk0 R I r) +
        DirectSum.of (grPiece R I) 0 (grMk0 R I s)
    rw [← map_add]
    congr 1

/-- The coefficient map `R ⧸ I → gr`, factoring `degZeroHom` through the
quotient by `Ideal.Quotient.lift` (no M4a identification needed).
-/
def coeffHom : R ⧸ I →+* associatedGraded R I :=
  Ideal.Quotient.lift I (degZeroHom R I) (fun a ha => by
    change DirectSum.of (grPiece R I) 0 (grMk0 R I a) = 0
    rw [← map_zero (DirectSum.of (grPiece R I) 0)]
    congr 1
    change (Submodule.Quotient.mk (⟨a, _⟩ : ↥(I ^ 0)) : grPiece R I 0) = 0
    rw [grPiece_mk_eq_zero_iff]
    change a ∈ I ^ (0 + 1)
    rw [show (0 : ℕ) + 1 = 1 from rfl, pow_one]
    exact ha)

/-- Computation rule for the coefficient map. -/
@[simp]
theorem coeffHom_mk (r : R) :
    coeffHom R I (Ideal.Quotient.mk I r) =
      DirectSum.of (grPiece R I) 0 (grMk0 R I r) :=
  rfl

/-! ## §2. The polynomial surjection -/

variable (d : ℕ) (g : Fin d → R)

/-- Each generator lies in `I ^ 1`. -/
theorem gen_mem_pow_one (i : Fin d) (hgen : Ideal.span (Set.range g) = I) :
    g i ∈ I ^ 1 := by
  rw [pow_one, ← hgen]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- Membership in `I ^ 1` transfers to the generator span. Stated for an
opaque `x` so the rewrites never meet a subtype coercion. -/
theorem mem_span_of_mem_pow_one (x : R) (hx : x ∈ I ^ 1)
    (hgen : Ideal.span (Set.range g) = I) : x ∈ Ideal.span (Set.range g) := by
  rw [hgen, ← pow_one I]
  exact hx

/-- The degree-1 class of a generator. -/
def genClass (i : Fin d) (hgen : Ideal.span (Set.range g) = I) :
    grPiece R I 1 :=
  Submodule.Quotient.mk (⟨g i, gen_mem_pow_one R I d g i hgen⟩ : ↥(I ^ 1))

/-- The canonical graded surjection from the polynomial ring over `R ⧸ I`,
via the universal property: constants through `coeffHom`, variables to the
degree-1 generator classes.
-/
def polySurj (hgen : Ideal.span (Set.range g) = I) :
    MvPolynomial (Fin d) (R ⧸ I) →+* associatedGraded R I :=
  MvPolynomial.eval₂Hom (coeffHom R I) fun i =>
    DirectSum.of (grPiece R I) 1 (genClass R I d g i hgen)

/-- Constants map through the coefficient map. -/
@[simp]
theorem polySurj_C (hgen : Ideal.span (Set.range g) = I) (a : R ⧸ I) :
    polySurj R I d g hgen (MvPolynomial.C a) = coeffHom R I a :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- Variables map to generator classes. -/
@[simp]
theorem polySurj_X (hgen : Ideal.span (Set.range g) = I) (i : Fin d) :
    polySurj R I d g hgen (MvPolynomial.X i) =
      DirectSum.of (grPiece R I) 1 (genClass R I d g i hgen) :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-! ## §3. Surjectivity degree by degree -/

/-- Scalars become degree-0 factors under `of`: `ofₙ (c • z)` is the product
of `of₀ [c]₀` with `ofₙ z`. This is what lets `R`-linear combinations in
`grPiece_span_mul_eq_top` lift to preimages under `polySurj`. -/
theorem of_smul_eq (n : ℕ) (c : R) (z : grPiece R I n) :
    DirectSum.of (grPiece R I) n (c • z) =
      DirectSum.of (grPiece R I) 0 (grMk0 R I c) *
        DirectSum.of (grPiece R I) n z := by
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I n z
  have hn : n = 0 + n := by omega
  rw [grPiece_mk_smul, associatedGraded_of_mul_of,
    of_cast_eq R I n (0 + n) hn]
  congr 1
  unfold grMk0
  -- Ground `e` first: `rw [grPiece_cast_mk]` with `e` a metavar spawns it as
  -- a side goal instead of matching it.
  have hcast := grPiece_cast_mk R I n (0 + n) hn (c • r)
  rw [hcast, grMul_mk_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  rw [grMulRep_apply]
  exact smul_eq_mul c (r : R)

/-- The `R`-submodule of degree-`k` classes hit by `polySurj`. -/
def preSubmodule (k : ℕ) (hgen : Ideal.span (Set.range g) = I) :
    Submodule R (grPiece R I k) where
  carrier := {z | ∃ p, polySurj R I d g hgen p = DirectSum.of (grPiece R I) k z}
  zero_mem' := ⟨0, by rw [map_zero, map_zero]; rfl⟩
  add_mem' := fun {a b} ⟨pa, hpa⟩ ⟨pb, hpb⟩ =>
    ⟨pa + pb, by rw [map_add, hpa, hpb, map_add]; rfl⟩
  smul_mem' := fun c z ⟨p, hp⟩ =>
    ⟨MvPolynomial.C (Ideal.Quotient.mk I c) * p, by
      rw [map_mul, polySurj_C, hp, coeffHom_mk]
      exact (of_smul_eq R I k c z).symm⟩

/-- Every degree-0 class is hit, via a constant polynomial. -/
theorem preimage_degree_zero (hgen : Ideal.span (Set.range g) = I)
    (z : grPiece R I 0) :
    ∃ p, polySurj R I d g hgen p = DirectSum.of (grPiece R I) 0 z := by
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I 0 z
  refine ⟨MvPolynomial.C (Ideal.Quotient.mk I (r : R)), ?_⟩
  rw [polySurj_C, coeffHom_mk]; rfl

/-- Every degree-1 class is hit, by span induction on the generators. -/
theorem preimage_degree_one (hgen : Ideal.span (Set.range g) = I)
    (z : grPiece R I 1) :
    ∃ p, polySurj R I d g hgen p = DirectSum.of (grPiece R I) 1 z := by
  obtain ⟨r, rfl⟩ := grPiece_mk_surjective R I 1 z
  have hle : Ideal.span (Set.range g) ≤ I ^ 1 := by rw [hgen, pow_one]
  have hmem : (r : R) ∈ Ideal.span (Set.range g) :=
    mem_span_of_mem_pow_one R I d g (r : R) r.2 hgen
  have r_eq : r = (⟨(r : R), hle hmem⟩ : ↥(I ^ 1)) := rfl
  rw [r_eq]
  refine Submodule.span_induction (p := fun x hx => ∃ p,
    polySurj R I d g hgen p = DirectSum.of (grPiece R I) 1
      (Submodule.Quotient.mk (⟨x, hle hx⟩ : ↥(I ^ 1)))) ?_ ?_ ?_ ?_ hmem
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    refine ⟨MvPolynomial.X i, ?_⟩
    rw [polySurj_X]; rfl
  · refine ⟨0, ?_⟩
    rw [map_zero]
    have hz : ∀ h : (0 : R) ∈ I ^ 1,
        (Submodule.Quotient.mk (⟨0, h⟩ : ↥(I ^ 1)) : grPiece R I 1) = 0 :=
      fun h => (grPiece_mk_eq_zero_iff R I 1 (⟨0, h⟩ : ↥(I ^ 1))).mpr
        (Submodule.zero_mem _)
    rw [hz]
    exact Eq.symm (map_zero (DirectSum.of (grPiece R I) 1))
  · intro x y hx hy ihx ihy
    obtain ⟨pa, hpa⟩ := ihx
    obtain ⟨pb, hpb⟩ := ihy
    refine ⟨pa + pb, ?_⟩
    rw [map_add, hpa, hpb]
    exact (map_add (DirectSum.of (grPiece R I) 1)
      (Submodule.Quotient.mk (⟨x, hle hx⟩ : ↥(I ^ 1)))
      (Submodule.Quotient.mk (⟨y, hle hy⟩ : ↥(I ^ 1)))).symm
  · intro c x hx ihx
    obtain ⟨p, hp⟩ := ihx
    refine ⟨MvPolynomial.C (Ideal.Quotient.mk I c) * p, ?_⟩
    rw [map_mul, polySurj_C, hp, coeffHom_mk]
    have hsmul := of_smul_eq R I 1 c
      (Submodule.Quotient.mk (⟨x, hle hx⟩ : ↥(I ^ 1)))
    rw [grPiece_mk_smul] at hsmul
    exact hsmul.symm

/-- Degree-`1 + n` classes are hit, via `grPiece_span_mul_eq_top`: products of
hit degree-1 and degree-`n` classes are hit, and they span. -/
theorem preimage_degree_succ (hgen : Ideal.span (Set.range g) = I) (n : ℕ)
    (ih : ∀ z : grPiece R I n,
      ∃ p, polySurj R I d g hgen p = DirectSum.of (grPiece R I) n z)
    (z : grPiece R I (1 + n)) :
    ∃ p, polySurj R I d g hgen p = DirectSum.of (grPiece R I) (1 + n) z := by
  have hle : ⊤ ≤ preSubmodule R I d g (1 + n) hgen := by
    rw [← grPiece_span_mul_eq_top R I n]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨a, b, rfl⟩ := hz
    obtain ⟨pa, hpa⟩ := preimage_degree_one R I d g hgen a
    obtain ⟨pb, hpb⟩ := ih b
    exact ⟨pa * pb, by
      rw [map_mul, hpa, hpb]
      exact associatedGraded_of_mul_of R I 1 n a b⟩
  exact hle Submodule.mem_top

/-- Every homogeneous element is hit, by induction on degree. -/
theorem preimage_of (hgen : Ideal.span (Set.range g) = I) (n : ℕ)
    (z : grPiece R I n) :
    ∃ p, polySurj R I d g hgen p = DirectSum.of (grPiece R I) n z := by
  induction n with
  | zero => exact preimage_degree_zero R I d g hgen z
  | succ n ih =>
    revert z
    rw [show n + 1 = 1 + n from Nat.add_comm n 1]
    exact preimage_degree_succ R I d g hgen n ih

/-! ## §4. The surjection and its first-isomorphism form -/

/-- The canonical map is surjective.
-/
theorem polySurj_surjective (hgen : Ideal.span (Set.range g) = I) :
    Function.Surjective (polySurj R I d g hgen) := by
  intro y
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of i x => exact preimage_of R I d g hgen i x
  | add x y hx hy =>
    obtain ⟨px, hpx⟩ := hx
    obtain ⟨py, hpy⟩ := hy
    exact ⟨px + py, by rw [map_add, hpx, hpy]; rfl⟩

/-- First-isomorphism form for M4c: the polynomial ring modulo the kernel of
`polySurj` is `gr`. This is the exact shape M4c-ii (dim-equality forces
injectivity) consumes.
-/
noncomputable def polySurj_quotKerEquiv (hgen : Ideal.span (Set.range g) = I) :
    MvPolynomial (Fin d) (R ⧸ I) ⧸ RingHom.ker (polySurj R I d g hgen) ≃+*
      associatedGraded R I :=
  RingHom.quotientKerEquivOfSurjective (polySurj_surjective R I d g hgen)

/-! ## §5. The `R_P` specialization for M4c -/

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

/-- Residue-field form of the surjection over the regular local ring `R_P`:
`MvPolynomial (Fin d) κ →+* grRegular P` for `d` generators of the maximal
ideal, where `κ` is the residue field. Definitionally the general `polySurj`.
-/
noncomputable def polySurjResidue (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    MvPolynomial (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime P)) →+*
      grRegular P :=
  polySurj (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) d g hgen

/-- The residue-field surjection is surjective.
-/
theorem polySurjResidue_surjective (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    Function.Surjective (polySurjResidue P d g hgen) :=
  polySurj_surjective (Localization.AtPrime P) (IsLocalRing.maximalIdeal _) d g
    hgen

/-- First-isomorphism form over the residue field: the polynomial ring in `d`
variables over `κ` modulo the kernel is `grRegular P`. This is the exact shape
M4c-ii consumes: with `dim` equality against the domain, `ker = ⊥`.
-/
noncomputable def polySurjResidue_quotKerEquiv (d : ℕ)
    (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    MvPolynomial (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime P)) ⧸
        RingHom.ker (polySurjResidue P d g hgen) ≃+* grRegular P :=
  RingHom.quotientKerEquivOfSurjective (polySurjResidue_surjective P d g hgen)

#print axioms polySurj_surjective
#print axioms polySurj_quotKerEquiv
#print axioms polySurjResidue_surjective

end GradedSurjection
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
