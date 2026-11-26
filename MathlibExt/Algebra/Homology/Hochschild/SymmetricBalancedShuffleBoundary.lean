/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricBalancedCuts
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyAdapter

/-!
# The signed Leibniz law for balanced Hochschild shuffles

Let k be a commutative ring, A a commutative k-algebra and M a compatible A-module. Signed
shuffle multiplication descends from the ground tensor product to the A-balanced coefficient
product. For positive input degrees r+1 and s+1, its Hochschild boundary is the shuffle of the
first boundary plus (-1)ʳ⁺¹ times the shuffle of the second boundary. The regular first
coefficient is ULift A; the second coefficient is M.

For signed shuffle chain maps, see J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- Balanced signed shuffle at an explicitly equal total degree.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, p+q=n gives an A-linear map from the A-balanced regular p-word/M-coefficient q-word
pair to M ⊗[k] A⊗n, using all (p,q)-shuffle signs. -/
def algebraShufflePairCutAt (p q n : ℕ) (h : p + q = n) :
    (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[A] (M ⊗[k] TensorPower k q A) →ₗ[A]
      M ⊗[k] TensorPower k n A :=
  (TensorProduct.AlgebraTensorModule.lTensor A M (TensorPower.cast k A h).toLinearMap).comp
    (algebraShufflePairCut k A M p q)

/-- The explicit-degree shuffle at its reflexive sum degree.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, taking n=p+q and h=rfl recovers algebraShufflePairCut(p,q). -/
@[simp]
theorem algebraShufflePairCutAt_refl (p q : ℕ) :
    algebraShufflePairCutAt k A M p q (p + q) rfl = algebraShufflePairCut k A M p q := by
  ext x
  simp only [algebraShufflePairCutAt, TensorPower.cast_refl, LinearEquiv.refl_toLinearMap,
    TensorProduct.AlgebraTensorModule.lTensor_id, LinearMap.id_comp]

/-- The explicit-degree balanced shuffle agrees with pairAt.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, restricting the balanced map to k and composing with algebraTensorComparison gives
pairAt(pairing,p,q,n,h) for the same equality p+q=n. -/
theorem algebraShufflePairCutAt_comparison (p q n : ℕ) (h : p + q = n) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  ((algebraShufflePairCutAt k A M p q n h).restrictScalars k).comp
    (algebraTensorComparison k A M p q) =
      (HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M) p q n h).hom := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  subst n
  rw [algebraShufflePairCutAt_refl, HomologicalComplex.ChainGradedPairing.pairAt_rfl]
  exact algebraShufflePairCut_comparison k A M p q

private theorem nativePairAt_boundary_successors (r s : ℕ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
      (r + 1) (s + 1) (r + s + 2) (by omega) ≫ (chainComplex k A M).d (r + s + 2) (r + s + 1) =
    (((chainComplex k A (ULift.{w} A)).d (r + 1) r ⊗ₘ 𝟙 ((chainComplex k A M).X (s + 1))) ≫
      HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
        r (s + 1) (r + s + 1) (by omega)) +
    (-1 : ℤ) ^ (r + 1) •
      ((𝟙 ((chainComplex k A (ULift.{w} A)).X (r + 1)) ⊗ₘ (chainComplex k A M).d (s + 1) s) ≫
        HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
          (r + 1) s (r + s + 1) (by omega)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  dsimp only [HomologicalComplex.ChainGradedPairing.pairAt]
  rw [Category.assoc, (pairing.{u, v, w} k A M).comm, ← Category.assoc,
    HomologicalComplex.ιTensorObj_comp_d_down_nat]
  have hr : r + 1 - 1 = r := by omega
  have hs : s + 1 - 1 = s := by omega
  simp only [dite_eq_right (by omega : r + 1 ≠ 0), dite_eq_right (by omega : s + 1 ≠ 0),
    hr, hs, Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
  let leftTerm (i : {i : ℕ // i + (s + 1) = r + s + 1}) :=
    (((chainComplex k A (ULift.{w} A)).d (r + 1) i.val ⊗ₘ 𝟙 ((chainComplex k A M).X (s + 1))) ≫
      HomologicalComplex.ιTensorObj (chainComplex k A (ULift.{w} A)) (chainComplex k A M)
        i.val (s + 1) (r + s + 1) i.property) ≫ (pairing.{u, v, w} k A M).f (r + s + 1)
  let rightTerm (j : {j : ℕ // (r + 1) + j = r + s + 1}) :=
    ((-1 : ℤ) ^ (r + 1) •
      (𝟙 ((chainComplex k A (ULift.{w} A)).X (r + 1)) ⊗ₘ (chainComplex k A M).d (s + 1) j.val)) ≫
      HomologicalComplex.ιTensorObj (chainComplex k A (ULift.{w} A)) (chainComplex k A M)
        (r + 1) j.val (r + s + 1) j.property ≫ (pairing.{u, v, w} k A M).f (r + s + 1)
  have hleftIndex : (⟨r + 1 - 1, by omega⟩ : {i : ℕ // i + (s + 1) = r + s + 1}) =
      ⟨r, by omega⟩ := Subtype.ext hr
  have hrightIndex : (⟨s + 1 - 1, by omega⟩ : {j : ℕ // (r + 1) + j = r + s + 1}) =
      ⟨s, by omega⟩ := Subtype.ext hs
  have htransport := congrArg₂ (· + ·) (congrArg leftTerm hleftIndex) (congrArg rightTerm hrightIndex)
  simpa only [leftTerm, rightTerm, Category.assoc, Preadditive.zsmul_comp] using htransport

/-- The Leibniz boundary formula for two positive balanced shuffle inputs.

For a commutative ring k, a commutative k-algebra A and an A-module M with compatible
k-action, bʀ⁺ˢ⁺¹ ∘ shʀ⁺¹,ˢ⁺¹ = shʀ,ˢ⁺¹ ∘ (bʀ,ULift A ⊗ id) + (-1)ʀ⁺¹ shʀ⁺¹,ˢ ∘ (id ⊗ bˢ,M).
Every map retains the displayed source and total degrees. -/
theorem algebraShufflePairCutAt_boundary_successors (r s : ℕ) :
    (algebraBoundary k A M (r + s + 1)).comp
      (algebraShufflePairCutAt k A M (r + 1) (s + 1) (r + s + 2) (by omega)) =
      (algebraShufflePairCutAt k A M r (s + 1) (r + s + 1) (by omega)).comp
        (TensorProduct.map (algebraBoundary k A (ULift.{w} A) r) LinearMap.id) +
      (-1 : ℤ) ^ (r + 1) •
        (algebraShufflePairCutAt k A M (r + 1) s (r + s + 1) (by omega)).comp
          (TensorProduct.map LinearMap.id (algebraBoundary k A M s)) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  apply LinearMap.restrictScalars_injective k
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := algebraTensorComparison_surjective k A M (r + 1) (s + 1) z
  have hn := nativePairAt_boundary_successors k A M r s
  have hx := ConcreteCategory.congr_hom hn x
  have hleft :
      TensorProduct.map (algebraBoundary k A (ULift.{w} A) r) LinearMap.id
        (algebraTensorComparison k A M (r + 1) (s + 1) x) =
      algebraTensorComparison k A M r (s + 1)
        (TensorProduct.map
          (((chainComplex k A (ULift.{w} A)).d (r + 1) r).hom) LinearMap.id x) := by
    let F : (ULift.{w} A ⊗[k] TensorPower k (r + 1) A) ⊗[k]
        (M ⊗[k] TensorPower k (s + 1) A) →ₗ[k]
        (ULift.{w} A ⊗[k] TensorPower k r A) ⊗[A] (M ⊗[k] TensorPower k (s + 1) A) :=
      ((TensorProduct.map (algebraBoundary k A (ULift.{w} A) r) LinearMap.id).restrictScalars k).comp
        (algebraTensorComparison k A M (r + 1) (s + 1))
    let G : (ULift.{w} A ⊗[k] TensorPower k (r + 1) A) ⊗[k]
        (M ⊗[k] TensorPower k (s + 1) A) →ₗ[k]
        (ULift.{w} A ⊗[k] TensorPower k r A) ⊗[A] (M ⊗[k] TensorPower k (s + 1) A) :=
      (algebraTensorComparison k A M r (s + 1)).comp
        (TensorProduct.map (((chainComplex k A (ULift.{w} A)).d (r + 1) r).hom) LinearMap.id)
    have heq : F = G := by
      apply TensorProduct.ext'
      intro u v
      change TensorProduct.map (algebraBoundary k A (ULift.{w} A) r) LinearMap.id
          (algebraTensorComparison k A M (r + 1) (s + 1) (u ⊗ₜ[k] v)) =
        algebraTensorComparison k A M r (s + 1)
          (TensorProduct.map (((chainComplex k A (ULift.{w} A)).d (r + 1) r).hom) LinearMap.id
            (u ⊗ₜ[k] v))
      rw [algebraTensorComparison_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
      have hmap := TensorProduct.map_tmul
        (((chainComplex k A (ULift.{w} A)).d (r + 1) r).hom)
        (LinearMap.id : M ⊗[k] TensorPower k (s + 1) A →ₗ[k] M ⊗[k] TensorPower k (s + 1) A) u v
      exact ((congrArg (algebraTensorComparison k A M r (s + 1)) hmap).trans
        (algebraTensorComparison_tmul k A M r (s + 1)
          ((((chainComplex k A (ULift.{w} A)).d (r + 1) r).hom) u) v)).symm
    exact LinearMap.congr_fun heq x
  have hright :
      TensorProduct.map LinearMap.id (algebraBoundary k A M s)
        (algebraTensorComparison k A M (r + 1) (s + 1) x) =
      algebraTensorComparison k A M (r + 1) s
        (TensorProduct.map LinearMap.id (((chainComplex k A M).d (s + 1) s).hom) x) := by
    let F : (ULift.{w} A ⊗[k] TensorPower k (r + 1) A) ⊗[k]
        (M ⊗[k] TensorPower k (s + 1) A) →ₗ[k]
        (ULift.{w} A ⊗[k] TensorPower k (r + 1) A) ⊗[A] (M ⊗[k] TensorPower k s A) :=
      ((TensorProduct.map LinearMap.id (algebraBoundary k A M s)).restrictScalars k).comp
        (algebraTensorComparison k A M (r + 1) (s + 1))
    let G : (ULift.{w} A ⊗[k] TensorPower k (r + 1) A) ⊗[k]
        (M ⊗[k] TensorPower k (s + 1) A) →ₗ[k]
        (ULift.{w} A ⊗[k] TensorPower k (r + 1) A) ⊗[A] (M ⊗[k] TensorPower k s A) :=
      (algebraTensorComparison k A M (r + 1) s).comp
        (TensorProduct.map LinearMap.id (((chainComplex k A M).d (s + 1) s).hom))
    have heq : F = G := by
      apply TensorProduct.ext'
      intro u v
      change TensorProduct.map LinearMap.id (algebraBoundary k A M s)
          (algebraTensorComparison k A M (r + 1) (s + 1) (u ⊗ₜ[k] v)) =
        algebraTensorComparison k A M (r + 1) s
          (TensorProduct.map LinearMap.id (((chainComplex k A M).d (s + 1) s).hom) (u ⊗ₜ[k] v))
      rw [algebraTensorComparison_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
      have hmap := TensorProduct.map_tmul
        (LinearMap.id : ULift.{w} A ⊗[k] TensorPower k (r + 1) A →ₗ[k]
          ULift.{w} A ⊗[k] TensorPower k (r + 1) A)
        (((chainComplex k A M).d (s + 1) s).hom) u v
      exact ((congrArg (algebraTensorComparison k A M (r + 1) s) hmap).trans
        (algebraTensorComparison_tmul k A M (r + 1) s u
          ((((chainComplex k A M).d (s + 1) s).hom) v))).symm
    exact LinearMap.congr_fun heq x
  change (algebraBoundary k A M (r + s + 1))
      (algebraShufflePairCutAt k A M (r + 1) (s + 1) (r + s + 2) (by omega)
        (algebraTensorComparison k A M (r + 1) (s + 1) x)) =
    algebraShufflePairCutAt k A M r (s + 1) (r + s + 1) (by omega)
      (TensorProduct.map (algebraBoundary k A (ULift.{w} A) r) LinearMap.id
        (algebraTensorComparison k A M (r + 1) (s + 1) x)) +
    (-1 : ℤ) ^ (r + 1) • algebraShufflePairCutAt k A M (r + 1) s (r + s + 1) (by omega)
      (TensorProduct.map LinearMap.id (algebraBoundary k A M s)
        (algebraTensorComparison k A M (r + 1) (s + 1) x))
  rw [hleft, hright]
  change ((chainComplex k A M).d (r + s + 2) (r + s + 1)).hom
      ((HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
        (r + 1) (s + 1) (r + s + 2) (by omega)).hom x) =
    (HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
      r (s + 1) (r + s + 1) (by omega)).hom
      ((((chainComplex k A (ULift.{w} A)).d (r + 1) r) ⊗ₘ
        𝟙 ((chainComplex k A M).X (s + 1))).hom x) +
    (-1 : ℤ) ^ (r + 1) •
      (HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
        (r + 1) s (r + s + 1) (by omega)).hom
        ((𝟙 ((chainComplex k A (ULift.{w} A)).X (r + 1)) ⊗ₘ
          ((chainComplex k A M).d (s + 1) s)).hom x) at hx
  have htop := DFunLike.congr_fun
    (algebraShufflePairCutAt_comparison.{u, v, w} k A M (r + 1) (s + 1) (r + s + 2) (by omega)) x
  have hlt := congrArg (fun f => f x)
    (ModuleCat.UniverseTensor.hom_tensorHom.{u, max v w} (R := k)
      ((chainComplex k A (ULift.{w} A)).d (r + 1) r) (𝟙 ((chainComplex k A M).X (s + 1))))
  have hrt := congrArg (fun f => f x)
    (ModuleCat.UniverseTensor.hom_tensorHom.{u, max v w} (R := k)
      (𝟙 ((chainComplex k A (ULift.{w} A)).X (r + 1))) ((chainComplex k A M).d (s + 1) s))
  have hpl := DFunLike.congr_fun
    (algebraShufflePairCutAt_comparison.{u, v, w} k A M r (s + 1) (r + s + 1) (by omega))
      (TensorProduct.map (((chainComplex k A (ULift.{w} A)).d (r + 1) r).hom) LinearMap.id x)
  have hpr := DFunLike.congr_fun
    (algebraShufflePairCutAt_comparison.{u, v, w} k A M (r + 1) s (r + s + 1) (by omega))
      (TensorProduct.map LinearMap.id (((chainComplex k A M).d (s + 1) s).hom) x)
  have hlvalue := (congrArg
    (fun y => (HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
      r (s + 1) (r + s + 1) (by omega)).hom y) hlt).trans hpl.symm
  have hrvalue := (congrArg
    (fun y => (HomologicalComplex.ChainGradedPairing.pairAt (pairing.{u, v, w} k A M)
      (r + 1) s (r + s + 1) (by omega)).hom y) hrt).trans hpr.symm
  exact (congrArg ((chainComplex k A M).d (r + s + 2) (r + s + 1)).hom htop).trans
    (hx.trans (congrArg₂ (· + ·) hlvalue (congrArg (fun y => (-1 : ℤ) ^ (r + 1) • y) hrvalue)))

end ModuleCat.Algebra.Hochschild.Symmetric
