/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplexRegularSequence
public import MathlibExt.LinearAlgebra.ExteriorPower.FinsuppFiniteSupport
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Koszul complexes of arbitrary coefficient families

For a family a : I → R in a commutative ring, the functional on the free module I →₀ R is the
finite linear combination v ↦ ∑ i, v_i a_i. Its exterior Koszul complex has terms ⋀[R]^n (I →₀
R), signed deletion boundaries, and augmentation to R/(a_i).

Every term is free and projective, even for an infinite index type I. If every finite ordered
subfamily of distinct indices is weakly regular, every positive-degree cycle is a boundary.
The quotient augmentation is then a quasi-isomorphism and defines a projective resolution of
the quotient, in the carrier universe enlarged to max u v. Finite-support exterior retractions
reduce the cycle computation to finite subfamilies.

See Weibel, *An Introduction to Homological Algebra*, Chapter 4, for Koszul complexes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace KoszulComplex

variable (R : Type u) [CommRing R] {I : Type v}

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. The map finsuppFunctional R a is this
linear combination functional; its value on the unit coordinate Finsupp.single i 1 is a_i. -/
def finsuppFunctional (a : I → R) : (I →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R a

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. For a finite subset s of I, composing
x_a with Finsupp.finsetInclude R s : (s → R) →ₗ[R] (I →₀ R) equals familyFunctional R (fun i :
s => a i.val). Thus the restricted finite family has the same functional values. -/
theorem finsuppFunctional_comp_finsetInclude (a : I → R) (s : Finset I) :
    (finsuppFunctional R a).comp (Finsupp.finsetInclude R s) =
      familyFunctional R (fun i : s => a i.val) := by
  classical
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, finsuppFunctional, Finsupp.finsetInclude_apply,
    map_sum, Finsupp.linearCombination_single, familyFunctional,
    Fintype.linearCombination_apply]

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. Assume that for every n : ℕ and
injective f : Fin n → I, the list [a_(f 0), …, a_(f(n−1))] is weakly regular over R, meaning
each coefficient acts injectively on the quotient by its predecessors. For k : ℕ and z :
⋀[R]^(k+1) (I →₀ R) with d_x(k)(z) = 0, there exists w : ⋀[R]^(k+2) (I →₀ R) such that
d_x(k+1)(w) = z. -/
theorem finsupp_exact_cycles_of_finite_isWeaklyRegular
    (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j)))
    (k : ℕ) (z : ⋀[R]^(k + 1) (I →₀ R))
    (hz : differential R (I →₀ R) (finsuppFunctional R a) k z = 0) :
    ∃ w : ⋀[R]^(k + 2) (I →₀ R),
      differential R (I →₀ R) (finsuppFunctional R a) (k + 1) w = z := by
  classical
  obtain ⟨s, zS, hzS⟩ := exteriorPower.exists_preimage_finset R (k + 1) z
  let aS : s → R := fun i => a i.val
  let inc := Finsupp.finsetInclude R s
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hregular : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => aS (e j)) :=
    ha (fun j => (e j).val) (Subtype.val_injective.comp e.injective)
  have hfunc : (finsuppFunctional R a).comp inc = familyFunctional R aS :=
    finsuppFunctional_comp_finsetInclude R a s
  have hcycle : differential R (s → R) (familyFunctional R aS) k zS = 0 := by
    apply exteriorPower.map_finsetInclude_injective R s k
    rw [map_zero]
    calc
      exteriorPower.map k inc
          (differential R (s → R) (familyFunctional R aS) k zS) =
          differential R (I →₀ R) (finsuppFunctional R a) k
            (exteriorPower.map (k + 1) inc zS) :=
        (LinearMap.congr_fun (differential_naturality R (s → R)
          (familyFunctional R aS) (finsuppFunctional R a) inc hfunc k) zS).symm
      _ = 0 := by rw [hzS, hz]
  obtain ⟨wS, hwS⟩ := family_exact_cycles_of_isWeaklyRegular R aS e hregular k zS hcycle
  refine ⟨exteriorPower.map (k + 2) inc wS, ?_⟩
  calc
    _ = exteriorPower.map (k + 1) inc
        (differential R (s → R) (familyFunctional R aS) (k + 1) wS) :=
      LinearMap.congr_fun (differential_naturality R (s → R)
        (familyFunctional R aS) (finsuppFunctional R a) inc hfunc (k + 1)) wS
    _ = z := by rw [hwS, hzS]

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. Define finsuppComplex R a as the
exterior Koszul complex with degree-n term ⋀[R]^n (I →₀ R) and boundary given by contraction
with x_a. For R : Type u and I : Type v it lies in ChainComplex (ModuleCat.{max u v} R) ℕ. -/
abbrev finsuppComplex (a : I → R) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  complex R (I →₀ R) (finsuppFunctional R a)

@[simp]
theorem finsuppFunctional_single (a : I → R) (i : I) :
    finsuppFunctional R a (Finsupp.single i 1) = a i := by
  classical
  rw [finsuppFunctional, Finsupp.linearCombination_single, one_smul]

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. For n : ℕ and any f : Fin (n + 1) → I,
write e_i = Finsupp.single i 1. Then d_x(n)(e_(f 0) ∧ … ∧ e_(f n)) = ∑ j : Fin (n + 1), ((−1 :
R)^j * a_(f j)) • (⋀ q : Fin n, e_(f(j.succAbove q))). The formula holds for every tuple, with
the undeleted coordinates in their original order. -/
theorem finsuppDifferential_apply_basis (a : I → R) (n : ℕ) (f : Fin (n + 1) → I) :
    differential R (I →₀ R) (finsuppFunctional R a) n
      (exteriorPower.ιMulti R (n + 1) (fun j => Finsupp.single (f j) 1)) =
    ∑ j : Fin (n + 1), (((-1 : R) ^ j.val) * a (f j)) •
      exteriorPower.ιMulti R n (fun q => Finsupp.single (f (j.succAbove q)) 1) := by
  rw [differential_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finsuppFunctional_single, smul_smul]
  rfl

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. For n : ℕ, p : R and f : Fin (n + 1) →
I, the boundary of p times the wedge of e_(f j) is ∑ j, (−1 : R)^j • ((p * a_(f j)) • (⋀ q :
Fin n, e_(f(j.succAbove q)))), where e_i is the unit coordinate at i. -/
theorem finsuppDifferential_smul_basis (a : I → R) (n : ℕ) (p : R)
    (f : Fin (n + 1) → I) :
    differential R (I →₀ R) (finsuppFunctional R a) n
      (p • exteriorPower.ιMulti R (n + 1) (fun j => Finsupp.single (f j) 1)) =
    ∑ j : Fin (n + 1), (-1 : R) ^ j.val •
      ((p * a (f j)) • exteriorPower.ιMulti R n
        (fun q => Finsupp.single (f (j.succAbove q)) 1)) := by
  rw [map_smul, finsuppDifferential_apply_basis, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [smul_smul]
  congr 1
  exact mul_left_comm p ((-1 : R) ^ j.val) (a (f j))

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. The ideal given by the range of x_a
equals Ideal.span (Set.range a), the ideal generated by all coefficients a_i. -/
theorem finsuppIdeal_eq_span (a : I → R) :
    ideal R (I →₀ R) (finsuppFunctional R a) = Ideal.span (Set.range a) := by
  change LinearMap.range (Finsupp.linearCombination R a) = _
  rw [Finsupp.range_linearCombination, Ideal.submodule_span_eq]

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. For every n : ℕ, the module
(finsuppComplex R a).X n = ⋀[R]^n (I →₀ R) is free over R. The index type I need not be
finite. -/
theorem finsuppComplex_free (a : I → R) (n : ℕ) :
    Module.Free R ((finsuppComplex R a).X n) := by
  change Module.Free R (⋀[R]^n (I →₀ R))
  infer_instance

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. For every n : ℕ, the degree-n object of
finsuppComplex R a is projective in ModuleCat.{max u v} R, using a basis of the exterior power
of the free coordinate module. -/
theorem finsuppComplex_projective (a : I → R) (n : ℕ) :
    CategoryTheory.Projective ((finsuppComplex R a).X n) := by
  classical
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  change CategoryTheory.Projective (ModuleCat.of R (⋀[R]^n (I →₀ R)))
  exact ModuleCat.projective_of_free ((Finsupp.basisSingleOne (R := R)).exteriorPower n)

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. The augmentation is the Koszul chain
map to the complex concentrated in degree zero at the lifted quotient R ⧸ Ideal.span
(Set.range a). In degree zero it is the zero-exterior scalar map followed by the quotient map;
its positive-degree components are zero. -/
abbrev finsuppAugmentation (a : I → R) := augmentation R (I →₀ R) (finsuppFunctional R a)

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. The short complex K₁ ⟶ K₀ ⟶
ULift(R/(a_i)) formed by the Koszul boundary and quotient augmentation is exact. Under ⋀[R]^0
(I →₀ R) ≅ R, the boundary image and augmentation kernel are both the ideal generated by the
a_i. -/
theorem finsuppAugmentation_exact_zero (a : I → R) :
    (augmentationShortComplex R (I →₀ R) (finsuppFunctional R a)).Exact :=
  augmentation_exact_zero R (I →₀ R) (finsuppFunctional R a)

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. Assume that for every n : ℕ and
injective f : Fin n → I, the list [a_(f 0), …, a_(f(n−1))] is weakly regular over R, meaning
each coefficient acts injectively on the quotient by its predecessors. Then finsuppComplex R a
is exact at degree k + 1 for every k : ℕ. -/
theorem finsuppComplex_exactAt_of_finite_isWeaklyRegular (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j))) (k : ℕ) :
    (finsuppComplex R a).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff'
    (K := finsuppComplex R a) (j := k + 1) (i := k + 2) (k := k)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) by rfl))
    ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (k + 1) k by rfl)),
    CategoryTheory.ShortComplex.moduleCat_exact_iff]
  intro z hz
  change ((complex R (I →₀ R) (finsuppFunctional R a)).d (k + 1) k) z = 0 at hz
  rw [complex_d_succ] at hz
  change differential R (I →₀ R) (finsuppFunctional R a) k z = 0 at hz
  change ∃ w : ⋀[R]^(k + 2) (I →₀ R),
    ((complex R (I →₀ R) (finsuppFunctional R a)).d (k + 2) (k + 1)) w = z
  rw [complex_d_succ]
  exact finsupp_exact_cycles_of_finite_isWeaklyRegular R a ha k z hz

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. Assume that for every n : ℕ and
injective f : Fin n → I, the list [a_(f 0), …, a_(f(n−1))] is weakly regular over R, meaning
each coefficient acts injectively on the quotient by its predecessors. The Koszul augmentation
to the complex concentrated at the lifted quotient R/(a_i) is a quasi-isomorphism. It
identifies H₀ with that quotient and the positive homology with zero. -/
theorem finsuppAugmentation_quasiIso_of_finite_isWeaklyRegular (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j))) :
    QuasiIso (augmentation R (I →₀ R) (finsuppFunctional R a)) := by
  refine ⟨fun j => ?_⟩
  cases j with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso
          (S₂ := augmentationShortComplex R (I →₀ R) (finsuppFunctional R a)) ?_).mpr
          ⟨augmentation_exact_zero R (I →₀ R) (finsuppFunctional R a),
            (ModuleCat.epi_iff_surjective _).mpr
              (augmentationLinearLifted_surjective R (I →₀ R) (finsuppFunctional R a))⟩
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · simp only [Iso.refl_hom]
          exact complex_d_succ R (I →₀ R) (finsuppFunctional R a) 0
        · simp only [Iso.refl_hom]
          exact augmentation_f_zero R (I →₀ R) (finsuppFunctional R a)
      all_goals rfl
  | succ j =>
      rw [quasiIsoAt_iff_exactAt']
      · exact finsuppComplex_exactAt_of_finite_isWeaklyRegular R a ha j
      · exact ChainComplex.exactAt_succ_single_obj _ _

/-- Let R be a commutative ring, I any index type and a : I → R a coefficient family. Let x_a : (I
→₀ R) →ₗ[R] R send v to the finite sum ∑ i, v_i * a_i. Assume that for every n : ℕ and
injective f : Fin n → I, the list [a_(f 0), …, a_(f(n−1))] is weakly regular over R, meaning
each coefficient acts injectively on the quotient by its predecessors. For R : Type u and I :
Type v, the complex finsuppComplex R a, with its quotient augmentation and projective exterior
terms, defines a ProjectiveResolution of ModuleCat.of R (ULift.{max u v} (R ⧸ Ideal.span
(Set.range a))). -/
def finsuppProjectiveResolutionOfFiniteIsWeaklyRegular (a : I → R)
    (ha : ∀ {n : ℕ}, ∀ f : Fin n → I, Function.Injective f →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn fun j => a (f j))) :
    ProjectiveResolution (ModuleCat.of R (ULift.{max u v, u}
      (R ⧸ ideal R (I →₀ R) (finsuppFunctional R a)))) where
  complex := finsuppComplex R a
  projective := finsuppComplex_projective R a
  π := augmentation R (I →₀ R) (finsuppFunctional R a)
  quasiIso := finsuppAugmentation_quasiIso_of_finite_isWeaklyRegular R a ha

end KoszulComplex
