/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.ProjectiveComparison
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Rank on projective-module K-zero

For a commutative ring `R`, a finitely generated projective module has a
locally constant rank on `PrimeSpectrum R`.  Pointwise addition and
multiplication of these rank functions agree with direct sum and tensor
product, so rank extends to a ring homomorphism

`RingK0 R →+* LocallyConstant (PrimeSpectrum R) ℤ`.

The construction reuses `Module.rankAtStalk` and the existing comparison
between the Grothendieck ring of projective classes and exact-category `K₀`.
It introduces no alternate rank function or K-theory carrier.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory ZeroObject
open Algebra

universe u

namespace FGProjectiveCat

variable {R : Type u} [CommRing R]

/-- The locally constant natural-valued rank of a finitely generated
projective module on `PrimeSpectrum R`. -/
noncomputable def rank (P : FGProjectiveCat.{u} R) :
    LocallyConstant (PrimeSpectrum R) ℕ where
  toFun := Module.rankAtStalk (R := R) P
  isLocallyConstant := by
    let _ : Module.FinitePresentation R P :=
      Module.finitePresentation_of_projective R P
    exact Module.isLocallyConstant_rankAtStalk

/-- Evaluation of the bundled projective rank is `Module.rankAtStalk`. -/
@[simp]
theorem rank_apply (P : FGProjectiveCat.{u} R) (p : PrimeSpectrum R) :
    rank P p = Module.rankAtStalk (R := R) P p :=
  rfl

/-- Integer-valued projective rank, used to pass to the Grothendieck group. -/
noncomputable def rankInt (P : FGProjectiveCat.{u} R) :
    LocallyConstant (PrimeSpectrum R) ℤ :=
  (rank P).map Int.ofNat

/-- Evaluation of integer-valued projective rank. -/
@[simp]
theorem rankInt_apply (P : FGProjectiveCat.{u} R) (p : PrimeSpectrum R) :
    rankInt P p = (Module.rankAtStalk (R := R) P p : ℤ) :=
  rfl

/-- Isomorphic projective modules have the same locally constant rank. -/
theorem rank_eq_of_iso {P Q : FGProjectiveCat.{u} R} (e : P ≅ Q) :
    rank P = rank Q := by
  ext p
  exact congr_fun
    (Module.rankAtStalk_eq_of_equiv (FGProjectiveCat.isoToLinearEquiv e)) p

/-- Isomorphic projective modules have the same integer-valued rank. -/
theorem rankInt_eq_of_iso {P Q : FGProjectiveCat.{u} R} (e : P ≅ Q) :
    rankInt P = rankInt Q := by
  ext p
  change (Module.rankAtStalk (R := R) P p : ℤ) =
    (Module.rankAtStalk (R := R) Q p : ℤ)
  exact_mod_cast congr_fun
    (Module.rankAtStalk_eq_of_equiv (FGProjectiveCat.isoToLinearEquiv e)) p

/-- The zero projective module has rank zero. -/
@[simp]
theorem rankInt_zero :
    rankInt (0 : FGProjectiveCat.{u} R) = 0 := by
  let _ : Subsingleton ((0 : FGProjectiveCat.{u} R) : Type u) :=
    ModuleCat.subsingleton_of_isZero
      ((FGProjectiveCat.toModuleCat (R := R)).map_isZero
        (isZero_zero (FGProjectiveCat.{u} R)))
  ext p
  change (Module.rankAtStalk (R := R) (0 : FGProjectiveCat.{u} R) p : ℤ) = 0
  have h := congr_fun
    (Module.rankAtStalk_eq_zero_of_subsingleton
      (R := R) (M := (0 : FGProjectiveCat.{u} R))) p
  exact_mod_cast h

private noncomputable def biprodLinearEquiv (P Q : FGProjectiveCat.{u} R) :
    ((P ⊞ Q : FGProjectiveCat.{u} R) : Type u) ≃ₗ[R] (P × Q) := by
  let F := FGProjectiveCat.toModuleCat (R := R)
  let _ : PreservesBiproduct (pairFunction P Q) F := inferInstance
  let _ : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F P Q
  exact ((F.mapBiprod P Q).trans
    (ModuleCat.biprodIsoProd P.obj Q.obj)).toLinearEquiv

/-- Direct sums add locally constant integer-valued ranks. -/
@[simp]
theorem rankInt_biprod (P Q : FGProjectiveCat.{u} R) :
    rankInt (P ⊞ Q) = rankInt P + rankInt Q := by
  ext p
  change (Module.rankAtStalk (R := R)
      ((P ⊞ Q : FGProjectiveCat.{u} R) : Type u) p : ℤ) =
    (Module.rankAtStalk (R := R) P p : ℤ) +
      (Module.rankAtStalk (R := R) Q p : ℤ)
  have hEquiv :
      Module.rankAtStalk (R := R)
          ((P ⊞ Q : FGProjectiveCat.{u} R) : Type u) p =
        Module.rankAtStalk (R := R) (P × Q) p :=
    congr_fun
      (Module.rankAtStalk_eq_of_equiv (biprodLinearEquiv P Q)) p
  have hProd :
      Module.rankAtStalk (R := R) (P × Q) p =
        Module.rankAtStalk (R := R) P p +
          Module.rankAtStalk (R := R) Q p :=
    congr_fun (Module.rankAtStalk_prod (R := R) P Q) p
  exact_mod_cast hEquiv.trans hProd

/-- Tensor products multiply locally constant integer-valued ranks. -/
@[simp]
theorem rankInt_tensor (P Q : FGProjectiveCat.{u} R) :
    rankInt (P ⊗ Q) = rankInt P * rankInt Q := by
  ext p
  change (Module.rankAtStalk (R := R) (TensorProduct R P Q) p : ℤ) =
    (Module.rankAtStalk (R := R) P p : ℤ) *
      (Module.rankAtStalk (R := R) Q p : ℤ)
  have h := congr_fun
    (Module.rankAtStalk_tensorProduct (R := R) (M := P) Q) p
  exact_mod_cast h

/-- The tensor unit has constant rank one. -/
@[simp]
theorem rankInt_unit :
    rankInt (𝟙_ (FGProjectiveCat.{u} R)) = 1 := by
  ext p
  let _ : Nontrivial R := p.nontrivial
  change (Module.rankAtStalk (R := R) R p : ℤ) = 1
  rw [Module.rankAtStalk_self]
  rfl

/-- Projective rank commutes with extension of scalars, contravariantly on
prime spectra. -/
theorem rankInt_baseChange {S : Type u} [CommRing S]
    (f : R →+* S) (P : FGProjectiveCat.{u} R) :
    rankInt ((FGProjectiveCat.baseChange f).obj P) =
      LocallyConstant.comap
        (⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ :
          C(PrimeSpectrum S, PrimeSpectrum R))
        (rankInt P) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' rfl
  ext p
  change (Module.rankAtStalk (R := S) (TensorProduct R S P) p : ℤ) =
    (Module.rankAtStalk (R := R) P (PrimeSpectrum.comap f p) : ℤ)
  exact_mod_cast Module.rankAtStalk_baseChange (R := R) (M := P) p

end FGProjectiveCat

namespace AlgebraicKTheory
namespace RingK0

variable (R : Type u) [CommRing R]

/-- Rank on the projective-class skeleton, as a semiring homomorphism to
locally constant integer-valued functions. -/
noncomputable def skeletonRank :
    Skeleton (FGProjectiveCat.{u} R) →+*
      LocallyConstant (PrimeSpectrum R) ℤ where
  toFun X := FGProjectiveCat.rankInt X.out
  map_zero' := by
    calc
      FGProjectiveCat.rankInt ((0 : Skeleton (FGProjectiveCat.{u} R)).out) =
          FGProjectiveCat.rankInt (0 : FGProjectiveCat.{u} R) :=
        FGProjectiveCat.rankInt_eq_of_iso
          (fromSkeletonToSkeletonIso (0 : FGProjectiveCat.{u} R))
      _ = 0 := FGProjectiveCat.rankInt_zero
  map_add' X Y := by
    calc
      FGProjectiveCat.rankInt (X + Y).out =
          FGProjectiveCat.rankInt (X.out ⊞ Y.out) :=
        FGProjectiveCat.rankInt_eq_of_iso
          (fromSkeletonToSkeletonIso (X.out ⊞ Y.out))
      _ = FGProjectiveCat.rankInt X.out + FGProjectiveCat.rankInt Y.out :=
        FGProjectiveCat.rankInt_biprod X.out Y.out
  map_one' := by
    calc
      FGProjectiveCat.rankInt (1 : Skeleton (FGProjectiveCat.{u} R)).out =
          FGProjectiveCat.rankInt (𝟙_ (FGProjectiveCat.{u} R)) :=
        FGProjectiveCat.rankInt_eq_of_iso
          (fromSkeletonToSkeletonIso (𝟙_ (FGProjectiveCat.{u} R)))
      _ = 1 := FGProjectiveCat.rankInt_unit
  map_mul' X Y := by
    calc
      FGProjectiveCat.rankInt (X * Y).out =
          FGProjectiveCat.rankInt (X.out ⊗ Y.out) :=
        FGProjectiveCat.rankInt_eq_of_iso
          (fromSkeletonToSkeletonIso (X.out ⊗ Y.out))
      _ = FGProjectiveCat.rankInt X.out * FGProjectiveCat.rankInt Y.out :=
        FGProjectiveCat.rankInt_tensor X.out Y.out

/-- Skeleton rank evaluates on the class of a projective module as its
integer-valued stalk rank. -/
@[simp]
theorem skeletonRank_toSkeleton (P : FGProjectiveCat.{u} R) :
    skeletonRank R (toSkeleton P) = FGProjectiveCat.rankInt P := by
  change FGProjectiveCat.rankInt (toSkeleton P).out = _
  exact FGProjectiveCat.rankInt_eq_of_iso (fromSkeletonToSkeletonIso P)

/-- Rank on the Grothendieck ring of projective isomorphism classes. -/
noncomputable def projectiveClassRank :
    GrothendieckAddGroup (Skeleton (FGProjectiveCat.{u} R)) →+*
      LocallyConstant (PrimeSpectrum R) ℤ :=
  GrothendieckAddGroup.liftRing (skeletonRank R)

/-- The rank ring homomorphism on projective-module `K₀`. -/
noncomputable def rank :
    RingK0 R →+* LocallyConstant (PrimeSpectrum R) ℤ :=
  (projectiveClassRank R).comp
    (K0.splitRingIso (FGProjectiveCat.{u} R)).inv.hom

/-- The rank of a projective-module generator is its locally constant stalk
rank. -/
@[simp]
theorem rank_mk (P : FGProjectiveCat.{u} R) :
    rank R (K0.mk P) = FGProjectiveCat.rankInt P := by
  rw [rank, RingHom.comp_apply, K0.splitRingIso_inv_mk]
  exact (GrothendieckAddGroup.liftRing_of (skeletonRank R) (toSkeleton P)).trans
    (skeletonRank_toSkeleton R P)

/-- Rank preserves zero. -/
@[simp]
theorem rank_zero : rank R 0 = 0 :=
  map_zero (rank R)

/-- Rank preserves addition. -/
@[simp]
theorem rank_add (x y : RingK0 R) : rank R (x + y) = rank R x + rank R y :=
  map_add (rank R) x y

/-- Rank preserves one. -/
@[simp]
theorem rank_one : rank R 1 = 1 :=
  map_one (rank R)

/-- Rank preserves multiplication. -/
@[simp]
theorem rank_mul (x y : RingK0 R) : rank R (x * y) = rank R x * rank R y :=
  map_mul (rank R) x y

/-- Rank is natural under extension of scalars; on spectra this is pullback
along the map induced by the ring homomorphism. -/
theorem rank_naturality {S : Type u} [CommRing S] (f : R →+* S) :
    (rank S).comp (RingK0.functor.map (CommRingCat.ofHom f)).hom =
      (LocallyConstant.comapRingHom
        (⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩ :
          C(PrimeSpectrum S, PrimeSpectrum R))).comp (rank R) := by
  let specMap : C(PrimeSpectrum S, PrimeSpectrum R) :=
    ⟨PrimeSpectrum.comap f, PrimeSpectrum.continuous_comap f⟩
  have hAdd :
      ((rank S).comp (RingK0.functor.map (CommRingCat.ofHom f)).hom).toAddMonoidHom =
        ((LocallyConstant.comapRingHom specMap).comp (rank R)).toAddMonoidHom := by
    apply K0.hom_ext
    intro P
    change rank S ((RingK0.functor.map (CommRingCat.ofHom f)).hom (K0.mk P)) =
      LocallyConstant.comapRingHom specMap (rank R (K0.mk P))
    rw [RingK0.functor_map_mk, rank_mk, rank_mk]
    exact FGProjectiveCat.rankInt_baseChange f P
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun hAdd x

/-- The reduced projective `K₀` ideal, defined as the kernel of rank. -/
abbrev reducedIdeal : Ideal (RingK0 R) :=
  RingHom.ker (rank R)

/-- Membership in reduced `K₀` means vanishing locally constant rank. -/
@[simp]
theorem mem_reducedIdeal_iff (x : RingK0 R) :
    x ∈ reducedIdeal R ↔ rank R x = 0 :=
  RingHom.mem_ker

end RingK0
end AlgebraicKTheory

end
