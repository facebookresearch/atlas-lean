/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorComposition

/-!
# The actual identity of the generic sphere operator coend

The identity is the whole degree-zero coefficient at the original index unitor.
Both composition-unit laws are checked on whole coefficient/coend generators.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

/-- The complete identity-labelled first operator composition is the original right-unitor label. -/
theorem identityLabel_left (a n k : I) (f : a ⊗ n ⟶ k) :
    compositionLabel n n k (CostructuredArrow.mk (Y := 𝟙_ I) (λ_ n).hom)
      (CostructuredArrow.mk (Y := a) f) = ((ρ_ a).hom ▷ n) ≫ f :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ f) (triangle a n))

/-- The complete identity-labelled last operator composition is the original left-unitor label. -/
theorem identityLabel_right (a n k : I) (f : a ⊗ n ⟶ k) :
    compositionLabel n k k (CostructuredArrow.mk (Y := a) f)
      (CostructuredArrow.mk (Y := 𝟙_ I) (λ_ k).hom) = ((λ_ a).hom ▷ n) ≫ f := by
  have hn := leftUnitor_naturality f
  have ha : (α_ (𝟙_ I) a n).hom ≫ (λ_ (a ⊗ n)).hom = (λ_ a).hom ▷ n := by
    rw [leftUnitor_tensor_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact (congrArg (fun t => (α_ (𝟙_ I) a n).hom ≫ t) hn).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ f) ha))

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- The actual operator identity is the entire degree-zero coefficient at the index unitor. -/
def identity (T : V) (n : I) : 𝟙_ V ⟶ Hom T n n := generator T (𝟙_ I) n n (λ_ n).hom

/-- Every full generator retains the actual first identity-composition law. -/
theorem generator_identity_left (T : V) (a n k : I) (f : a ⊗ n ⟶ k) :
    ((𝟙_ V) ◁ generator T a n k f) ≫ (identity T n ▷ Hom T n k) ≫ composition T n n k =
      (λ_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫ generator T a n k f := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj a ⟶ Hom T n k := generator T a n k f
  let z : P.obj (a ⊗ (𝟙_ I)) ⟶ Hom T n k := generator T (a ⊗ (𝟙_ I)) n k
    (compositionLabel n n k (CostructuredArrow.mk (Y := 𝟙_ I) (λ_ n).hom)
      (CostructuredArrow.mk (Y := a) f))
  let m : P.obj a ⊗ (𝟙_ V) ⟶ P.obj (a ⊗ (𝟙_ I)) := (tensorPowObj_add T a.of.len 0).inv
  have hPrefix : ((𝟙_ V) ◁ j) ≫ (identity T n ▷ Hom T n k) = identity T n ⊗ₘ j :=
    (tensorHom_def' (identity T n) j).symm
  have hComp : (identity T n ⊗ₘ j) ≫ composition T n n k =
      (β_ (𝟙_ V) (P.obj a)).hom ≫ m ≫ z :=
    generator_composition T (𝟙_ I) a n n k (λ_ n).hom f
  have hLabel : z = P.map (ρ_ a).hom ≫ j :=
    (congrArg (generator T (a ⊗ (𝟙_ I)) n k) (identityLabel_left a n k f)).trans
      (generator_relation T (ρ_ a).hom f).symm
  have hPower : m ≫ P.map (ρ_ a).hom = (ρ_ (P.obj a)).hom :=
    genericSphereSequence_block_unit_right T a
  have hBraid : (β_ (𝟙_ V) (P.obj a)).hom ≫ (ρ_ (P.obj a)).hom = (λ_ (P.obj a)).hom := by
    rw [braiding_tensorUnit_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hMiddle : (β_ (𝟙_ V) (P.obj a)).hom ≫ m ≫ z =
      (λ_ (P.obj a)).hom ≫ j := by
    rw [hLabel]
    rw [← Category.assoc m, hPower]
    rw [← Category.assoc, hBraid]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ composition T n n k) hPrefix).trans (hComp.trans hMiddle))

/-- Every full generator retains the actual last identity-composition law. -/
theorem generator_identity_right (T : V) (a n k : I) (f : a ⊗ n ⟶ k) :
    (generator T a n k f ▷ (𝟙_ V)) ≫ (Hom T n k ◁ identity T k) ≫ composition T n k k =
      (ρ_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫ generator T a n k f := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj a ⟶ Hom T n k := generator T a n k f
  let z : P.obj ((𝟙_ I) ⊗ a) ⟶ Hom T n k := generator T ((𝟙_ I) ⊗ a) n k
    (compositionLabel n k k (CostructuredArrow.mk (Y := a) f)
      (CostructuredArrow.mk (Y := 𝟙_ I) (λ_ k).hom))
  let m : (𝟙_ V) ⊗ P.obj a ⟶ P.obj ((𝟙_ I) ⊗ a) := (tensorPowObj_add T 0 a.of.len).inv
  have hPrefix : (j ▷ (𝟙_ V)) ≫ (Hom T n k ◁ identity T k) = j ⊗ₘ identity T k :=
    (tensorHom_def j (identity T k)).symm
  have hComp : (j ⊗ₘ identity T k) ≫ composition T n k k =
      (β_ (P.obj a) (𝟙_ V)).hom ≫ m ≫ z :=
    generator_composition T a (𝟙_ I) n k k f (λ_ k).hom
  have hLabel : z = P.map (λ_ a).hom ≫ j :=
    (congrArg (generator T ((𝟙_ I) ⊗ a) n k) (identityLabel_right a n k f)).trans
      (generator_relation T (λ_ a).hom f).symm
  have hPower : m ≫ P.map (λ_ a).hom = (λ_ (P.obj a)).hom :=
    genericSphereSequence_block_unit_left T a
  have hBraid : (β_ (P.obj a) (𝟙_ V)).hom ≫ (λ_ (P.obj a)).hom = (ρ_ (P.obj a)).hom := by
    rw [braiding_tensorUnit_right, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hMiddle : (β_ (P.obj a) (𝟙_ V)).hom ≫ m ≫ z =
      (ρ_ (P.obj a)).hom ≫ j := by
    rw [hLabel]
    rw [← Category.assoc m, hPower]
    rw [← Category.assoc, hBraid]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ composition T n k k) hPrefix).trans (hComp.trans hMiddle))

/-- The first unit equation holds on the whole original operator Hom coend. -/
theorem identity_comp (T : V) (n k : I) :
    (identity T n ▷ Hom T n k) ≫ composition T n n k = (λ_ (Hom T n k)).hom := by
  apply (isColimitOfPreserves (tensorLeft (𝟙_ V)) (colimit.isColimit (diagram T n k))).hom_ext
  intro q
  exact (generator_identity_left T q.left n k q.hom).trans
    (leftUnitor_naturality (generator T q.left n k q.hom)).symm

/-- The last unit equation holds on the whole original operator Hom coend. -/
theorem comp_identity (T : V) (n k : I) :
    (Hom T n k ◁ identity T k) ≫ composition T n k k = (ρ_ (Hom T n k)).hom := by
  apply (isColimitOfPreserves (tensorRight (𝟙_ V)) (colimit.isColimit (diagram T n k))).hom_ext
  intro q
  exact (generator_identity_right T q.left n k q.hom).trans
    (rightUnitor_naturality (generator T q.left n k q.hom)).symm

end CategoryTheory.Spectra.Symmetric.OperatorCoend
