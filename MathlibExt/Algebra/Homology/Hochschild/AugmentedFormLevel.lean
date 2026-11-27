/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.AugmentedAlgebraFunctor
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjectionSurjective
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentHigherForms
public import MathlibExt.Algebra.Category.ModuleCat.CompatibleScalarRestriction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Coefficient differential forms and higher cotangent modules

Let `k` be a commutative ring and `P → B` an augmentation to a commutative `k`-algebra. The
coefficient differential-form module in weight `q` is `B ⊗[P] ⋀^q[P] Ω[P/k]`. Its lifted
Hochschild presentation is naturally isomorphic, over `k`, to the higher cotangent module over
`B` with scalars restricted to `k`.

The integral form projection sends `b ⊗ (a₀ ⊗ ⋯ ⊗ a_q)` to `b ⊗ (da₀ ∧ ⋯ ∧ da_q)` in positive
weight. Weight zero is identified through the regular tensor unitor `B ⊗[P] P ≅ B`. The
projection and the form-module comparison are natural in maps over `B`; their formulas retain
the coefficient value and use no factorial normalization.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v r s

namespace ModuleCat.Algebra.Hochschild.Symmetric.AugmentedAlgebra

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

attribute [local instance] CommAlgCat.cotangentAlgebra CommAlgCat.cotangentScalarTower

private theorem module_comp_value {R : Type r} [Ring R]
    {X Y Z : ModuleCat.{s} R} (a : X ⟶ Y) (b : Y ⟶ Z) (x : X) :
    (a ≫ b).hom x = b.hom (a.hom x) := rfl

private theorem module_eq_comp_value {R : Type r} [Ring R]
    {X Y Z : ModuleCat.{s} R} {f : X ⟶ Z} (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : f = a ≫ b) (x : X) : f.hom x = b.hom (a.hom x) :=
  (congrArg (fun g => g.hom x) h).trans (module_comp_value a b x)

private theorem module_iso_hom_inv_value {R : Type r} [Ring R]
    {X Y : ModuleCat.{s} R} (e : X ≅ Y) (y : Y) :
    e.hom.hom (e.inv.hom y) = y :=
  congrArg (fun f : Y ⟶ Y => f.hom y) e.inv_hom_id

private theorem module_iso_inv_hom_value {R : Type r} [Ring R]
    {X Y : ModuleCat.{s} R} (e : X ≅ Y) (x : X) :
    e.inv.hom (e.hom.hom x) = x :=
  congrArg (fun f : X ⟶ X => f.hom x) e.hom_inv_id

private theorem module_iso_hom_cancel {R : Type r} [Ring R]
    {X Y : ModuleCat.{s} R} (e : X ≅ Y) {x y : X}
    (h : e.hom.hom x = e.hom.hom y) : x = y :=
  (module_iso_inv_hom_value e x).symm.trans
    ((congrArg e.inv.hom h).trans (module_iso_inv_hom_value e y))

private theorem module_iso_after_trans_symm {R : Type r} [Ring R]
    {X Y Z : ModuleCat.{s} R} (a : X ≅ Z) (c : Y ≅ Z) (x : X) :
    c.hom.hom ((a ≪≫ c.symm).hom.hom x) = a.hom.hom x :=
  (congrArg c.hom.hom (module_comp_value a.hom c.inv x)).trans
    (module_iso_hom_inv_value c (a.hom.hom x))

private theorem restricted_map_value {R : Type r} [Ring R]
    {S : Type s} [Ring S] (φ : R →+* S)
    {X Y : ModuleCat.{max r s} S} (f : X ⟶ Y)
    (x : (ModuleCat.restrictScalars φ).obj X) :
    ((ModuleCat.restrictScalars φ).map f).hom x = f.hom x := rfl

private theorem restricted_map_value_eq {R : Type r} [Ring R]
    {S : Type s} [Ring S] (φ : R →+* S)
    {X Y : ModuleCat.{max r s} S} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f.hom x = y) :
    ((ModuleCat.restrictScalars φ).map f).hom
      (show (ModuleCat.restrictScalars φ).obj X from x) =
        (show (ModuleCat.restrictScalars φ).obj Y from y) :=
  (restricted_map_value φ f x).trans h

private theorem module_reassoc {R : Type r} [Ring R]
    {X Y A B Z : ModuleCat.{s} R} (c : X ⟶ Y) (q : Y ⟶ B)
    (p : X ⟶ A) (h : A ⟶ B) (e : c ≫ q = p ≫ h) (t : B ⟶ Z) :
    c ≫ q ≫ t = p ≫ h ≫ t :=
  (Category.assoc c q t).symm.trans
    ((congrArg (fun f => f ≫ t) e).trans (Category.assoc p h t))

private theorem follow_value {X Y Z : Type*} (f : X → Y) (g : Y → Z)
    (x : X) (y : Y) (z : Z) (hf : f x = y) (hg : g y = z) :
    g (f x) = z := (congrArg g hf).trans hg

private theorem commute_value {X Y A B : Type*} (c : X → Y)
    (p : X → A) (q : Y → B) (h : A → B)
    (x : X) (y : Y) (a : A) (b : B)
    (hc : c x = y) (hp : p x = a) (hq : q y = b) (hh : h a = b) :
    q (c x) = h (p x) :=
  (follow_value c q x y b hc hq).trans (follow_value p h x a b hp hh).symm

private theorem module_word_square {R : Type r} [Ring R]
    {X Y A B : ModuleCat.{s} R} (c : X ⟶ Y) (p : X ⟶ A)
    (t : Y ⟶ B) (h : A ⟶ B) (x : X) (y : Y) (a : A) (b : B)
    (hc : c.hom x = y) (hp : p.hom x = a)
    (ht : t.hom y = b) (hh : h.hom a = b) :
    (c ≫ t).hom x = (p ≫ h).hom x :=
  (module_comp_value c t x).trans
    ((follow_value c.hom t.hom x y b hc ht).trans
      ((follow_value p.hom h.hom x a b hp hh).symm.trans (module_comp_value p h x).symm))

/-- The higher cotangent functor restricted to ground scalars.

In weight `q`, this sends `P → B` to the `k`-module underlying the `B`-module `B ⊗[P] ⋀^q[P]
Ω[P/k]`, and maps over `B` to their higher differential maps. -/
def higherGroundFunctor (q : ℕ) : Over B ⥤ ModuleCat.{max u v} k where
  obj P := (ModuleCat.restrictScalars (algebraMap k B)).obj
    (CommAlgCat.cotangentHigherLevel.{u, v} k B q P)
  map f := (ModuleCat.restrictScalars (algebraMap k B)).map
    (CommAlgCat.cotangentHigherMap.{u, v} k B q f)
  map_id P :=
    (congrArg (ModuleCat.restrictScalars (algebraMap k B)).map
      (CommAlgCat.cotangentHigherMap_id.{u, v} k B q P)).trans
        ((ModuleCat.restrictScalars (algebraMap k B)).map_id _)
  map_comp f g :=
    (congrArg (ModuleCat.restrictScalars (algebraMap k B)).map
      (CommAlgCat.cotangentHigherMap_comp.{u, v} k B q f g)).trans
        ((ModuleCat.restrictScalars (algebraMap k B)).map_comp _ _)

/-- The scalar-restriction description of the higher ground functor.

The weight-`q` higher ground functor is the higher cotangent functor over `B` followed by
restriction of scalars along `k → B`. -/
theorem higherGroundFunctor_eq (q : ℕ) : higherGroundFunctor.{u, v} k B q =
    CommAlgCat.cotangentHigherFunctor.{u, v} k B q ⋙
      ModuleCat.restrictScalars (algebraMap k B) := rfl

/-- The object formula for higher ground cotangent modules.

At `P → B`, the weight-`q` object is scalar restriction of the higher cotangent module `B ⊗[P]
⋀^q[P] Ω[P/k]`. -/
theorem higherGroundFunctor_obj (q : ℕ) (P : Over B) :
    (higherGroundFunctor.{u, v} k B q).obj P =
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.cotangentHigherLevel.{u, v} k B q P) := rfl

/-- The morphism formula for higher ground cotangent modules.

For `f : P → Q` over `B`, the weight-`q` map is restriction of the higher cotangent map
induced by `f`. -/
theorem higherGroundFunctor_map {P Q : Over B} (f : P ⟶ Q) (q : ℕ) :
    (higherGroundFunctor.{u, v} k B q).map f =
      (ModuleCat.restrictScalars (algebraMap k B)).map
        (CommAlgCat.cotangentHigherMap.{u, v} k B q f) := rfl

/-- The lifted coefficient differential-form module.

For `P → B` and `q ∈ ℕ`, this is the `k`-module on the lifted carrier `ULift.{u}(B ⊗[P] ⋀^q[P]
Ω[P/k])`. -/
def rawFormLevel (q : ℕ) (P : Over B) : ModuleCat.{max u v} k := by
  letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  exact ModuleCat.of k
    (ULift.{u} (B ⊗[P.left] (⋀[P.left]^q (KaehlerDifferential k P.left))))

/-- The coefficient-form complex component in lifted coordinates.

The lifted coefficient differential-form module in weight `q` is the degree-`q` component of
the coefficient differential-form complex. -/
theorem rawFormLevel_eq (q : ℕ) (P : Over B) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    rawFormLevel.{u, v} k B q P = (Symmetric.coefficientDifferentialFormComplex k P.left B).X q := rfl

/-- The comparison from lifted forms to higher cotangent modules.

For every weight `q`, the lifted coefficient-form module is `k`-linearly isomorphic to the
ground restriction of the higher cotangent module. In positive weights the map removes the
carrier lift; weight zero uses the regular tensor unitor. -/
def rawFormLevelIso (q : ℕ) (P : Over B) :
    rawFormLevel.{u, v} k B q P ≅ (higherGroundFunctor.{u, v} k B q).obj P := by
  letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  cases q with
  | zero =>
      let T := B ⊗[P.left] (⋀[P.left]^0 (KaehlerDifferential k P.left))
      let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B 0 P
      let Y : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B 0).obj P
      let Z : ModuleCat.{max u v} k := ModuleCat.of k T
      let K : ModuleCat.{max u v} k := ModuleCat.of k B
      letI : Module k X := X.isModule
      letI : Module k Y := Y.isModule
      letI : Module k Z := Z.isModule
      letI : Module k K := K.isModule
      let l : X ≅ Z := (ULift.moduleEquiv : X ≃ₗ[k] Z).toModuleIso
      let e : Z ≅ K :=
        (((TensorProduct.congr (LinearEquiv.refl P.left B)
          (exteriorPower.zeroEquiv P.left (KaehlerDifferential k P.left))).trans
            (TensorProduct.rid P.left B)).restrictScalars k).toModuleIso
      let w : Y ≅ (ModuleCat.restrictScalars (algebraMap k B)).obj (ModuleCat.of B B) :=
        (ModuleCat.restrictScalars (algebraMap k B)).mapIso
          (CommAlgCat.cotangentWeightZeroLevelIso k B P)
      let a : (ModuleCat.restrictScalars (algebraMap k B)).obj (ModuleCat.of B B) ≅ K :=
        (ModuleCat.compatibleRestrictScalarsEquiv k B B).toModuleIso
      exact (l ≪≫ e) ≪≫ (w ≪≫ a).symm
  | succ q =>
      let T := B ⊗[P.left] (⋀[P.left]^(q + 1) (KaehlerDifferential k P.left))
      let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B (q + 1) P
      let Y : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B (q + 1)).obj P
      let Z : ModuleCat.{max u v} k := ModuleCat.of k T
      letI : Module k X := X.isModule
      letI : Module k Y := Y.isModule
      letI : Module k Z := Z.isModule
      let l : X ≅ Z := (ULift.moduleEquiv : X ≃ₗ[k] Z).toModuleIso
      let c : Y ≅ Z := (ModuleCat.compatibleRestrictScalarsEquiv k B T).toModuleIso
      exact l ≪≫ c.symm

/-- The lifted coefficient-form map of an augmented algebra map.

For `f : P → Q` over `B`, this is the degree-`q` differential-form map induced by `f`,
retaining the coefficient action through the augmentations. -/
def rawFormMap {P Q : Over B} (f : P ⟶ Q) (q : ℕ) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : Algebra Q.left B := CommAlgCat.cotangentAlgebra k B Q
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    letI : IsScalarTower k Q.left B := CommAlgCat.cotangentScalarTower k B Q
    rawFormLevel.{u, v} k B q P ⟶ rawFormLevel.{u, v} k B q Q := by
  letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  letI : Algebra Q.left B := CommAlgCat.cotangentAlgebra k B Q
  letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  letI : IsScalarTower k Q.left B := CommAlgCat.cotangentScalarTower k B Q
  exact (Symmetric.coefficientFormAlgebraComplexMap k f.left.hom
    (LinearMap.id : B →ₗ[k] B) (coefficientCompatibility k B f)).f q

/-- The degreewise description of a lifted coefficient-form map.

The lifted weight-`q` map is the degree-`q` component of the coefficient differential-form
complex map with algebra map `f` and identity coefficient map on `B`. -/
theorem rawFormMap_eq {P Q : Over B} (f : P ⟶ Q) (q : ℕ) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : Algebra Q.left B := CommAlgCat.cotangentAlgebra k B Q
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    letI : IsScalarTower k Q.left B := CommAlgCat.cotangentScalarTower k B Q
    let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q P
    let Y : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q Q
    let g : X ⟶ Y := rawFormMap k B f q
    let g' : X ⟶ Y := (Symmetric.coefficientFormAlgebraComplexMap k f.left.hom
      (LinearMap.id : B →ₗ[k] B) (coefficientCompatibility k B f)).f q
    g = g' := by
  dsimp only
  rfl

/-- The Hochschild projection to a higher cotangent module.

In degree `q`, compose the coefficient differential-form chain projection with the comparison
from lifted forms to the ground higher cotangent module of `P → B`. -/
def higherProjection (q : ℕ) (P : Over B) :
    (complex k B P).X q ⟶ (higherGroundFunctor.{u, v} k B q).obj P := by
  letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  exact (Symmetric.coefficientDifferentialFormChainMap k P.left B).f q ≫
    (rawFormLevelIso.{u, v} k B q P).hom

private theorem rawFormLevelIso_succ_hom_apply (q : ℕ) (P : Over B) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    let T := B ⊗[P.left] (⋀[P.left]^(q + 1) (KaehlerDifferential k P.left))
    let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B (q + 1) P
    let Y : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B (q + 1)).obj P
    let Z : ModuleCat.{max u v} k := ModuleCat.of k T
    let e : X ≅ Y := rawFormLevelIso.{u, v} k B (q + 1) P
    ∀ z : Z, e.hom.hom (ULift.up z) = (show Y from z) := by
  let : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  let : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  dsimp only
  intro (z : B ⊗[P.left] (⋀[P.left]^(q + 1) (KaehlerDifferential k P.left)))
  let T := B ⊗[P.left] (⋀[P.left]^(q + 1) (KaehlerDifferential k P.left))
  let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B (q + 1) P
  let Y : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B (q + 1)).obj P
  let Z : ModuleCat.{max u v} k := ModuleCat.of k T
  let : Module k X := X.isModule
  let : Module k Y := Y.isModule
  let : Module k Z := Z.isModule
  let l : X ≅ Z := (ULift.moduleEquiv : X ≃ₗ[k] Z).toModuleIso
  let c : Y ≅ Z := (ModuleCat.compatibleRestrictScalarsEquiv k B T).toModuleIso
  have hForward (y : Y) : c.hom.hom y = (show Z from y) :=
    ModuleCat.compatibleRestrictScalarsEquiv_apply k B T y
  have hLift : l.hom.hom (ULift.up z) = z := rfl
  have hValue : c.hom.hom ((rawFormLevelIso.{u, v} k B (q + 1) P).hom.hom (ULift.up z)) =
      l.hom.hom (ULift.up z) := module_iso_after_trans_symm l c (ULift.up z)
  exact (hForward _).symm.trans (hValue.trans hLift)

private theorem rawFormLevelIso_zero_hom_apply (P : Over B) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    ∀ z : B ⊗[P.left] (⋀[P.left]^0 (KaehlerDifferential k P.left)),
      (rawFormLevelIso.{u, v} k B 0 P).hom.hom (ULift.up z) =
        (CommAlgCat.cotangentWeightZeroLevelIso k B P).inv.hom
          (((TensorProduct.congr (LinearEquiv.refl P.left B)
            (exteriorPower.zeroEquiv P.left (KaehlerDifferential k P.left))).trans
              (TensorProduct.rid P.left B)).restrictScalars k z) := by
  let : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  let : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  intro z
  let T := B ⊗[P.left] (⋀[P.left]^0 (KaehlerDifferential k P.left))
  let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B 0 P
  let Y : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B 0).obj P
  let Z : ModuleCat.{max u v} k := ModuleCat.of k T
  let K : ModuleCat.{max u v} k := ModuleCat.of k B
  let : Module k X := X.isModule
  let : Module k Y := Y.isModule
  let : Module k Z := Z.isModule
  let : Module k K := K.isModule
  let l : X ≅ Z := (ULift.moduleEquiv : X ≃ₗ[k] Z).toModuleIso
  let e : Z ≅ K :=
    (((TensorProduct.congr (LinearEquiv.refl P.left B)
      (exteriorPower.zeroEquiv P.left (KaehlerDifferential k P.left))).trans
        (TensorProduct.rid P.left B)).restrictScalars k).toModuleIso
  let W := CommAlgCat.cotangentWeightZeroLevelIso k B P
  let w : Y ≅ (ModuleCat.restrictScalars (algebraMap k B)).obj (ModuleCat.of B B) :=
    (ModuleCat.restrictScalars (algebraMap k B)).mapIso W
  let a : (ModuleCat.restrictScalars (algebraMap k B)).obj (ModuleCat.of B B) ≅ K :=
    (ModuleCat.compatibleRestrictScalarsEquiv k B B).toModuleIso
  let c : Y ≅ K := w ≪≫ a
  have hForward (y : Y) : c.hom.hom y = W.hom.hom y :=
    (module_comp_value w.hom a.hom y).trans
      ((ModuleCat.compatibleRestrictScalarsEquiv_apply k B B (w.hom.hom y)).trans
        (restricted_map_value (algebraMap k B) W.hom y))
  have hLift : l.hom.hom (ULift.up z) = z := rfl
  have hValue : c.hom.hom ((rawFormLevelIso.{u, v} k B 0 P).hom.hom (ULift.up z)) = e.hom.hom z :=
    (module_iso_after_trans_symm (l ≪≫ e) c (ULift.up z)).trans
      ((module_comp_value l.hom e.hom (ULift.up z)).trans (congrArg e.hom.hom hLift))
  have hInverse : c.hom.hom (W.inv.hom (e.hom.hom z)) = e.hom.hom z :=
    (hForward _).trans (module_iso_hom_inv_value W (e.hom.hom z))
  exact module_iso_hom_cancel c (hValue.trans hInverse.symm)

/-- The value of the higher cotangent projection.

For a degree-`q` Hochschild chain `z`, the higher projection is the lifted coefficient-form
projection of `z` followed by the form-module comparison. -/
theorem higherProjection_apply (q : ℕ) (P : Over B) (z : (complex k B P).X q) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    (higherProjection.{u, v} k B q P).hom z =
      (rawFormLevelIso.{u, v} k B q P).hom.hom
        (((Symmetric.coefficientDifferentialFormChainMap k P.left B).f q).hom z) := by
  let : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  let : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  let X : ModuleCat.{max u v} k := (complex k B P).X q
  let T : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q P
  let Y : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B q).obj P
  let : Module k X := X.isModule
  let : Module k T := T.isModule
  let : Module k Y := Y.isModule
  let π := (Symmetric.coefficientDifferentialFormChainMap k P.left B).f q
  let e : T ⟶ Y := (rawFormLevelIso.{u, v} k B q P).hom
  exact module_comp_value π e z

private theorem higherGroundFunctor_map_apply {P Q : Over B} (f : P ⟶ Q)
    (q : ℕ) (z : (higherGroundFunctor.{u, v} k B q).obj P) :
    ((higherGroundFunctor.{u, v} k B q).map f).hom z =
      (CommAlgCat.cotangentHigherMap.{u, v} k B q f).hom z :=
  restricted_map_value (algebraMap k B) (CommAlgCat.cotangentHigherMap.{u, v} k B q f) z

/-- The differential-wedge formula for a higher cotangent projection.

In degree `q+1`, the projection sends `b ⊗ (a₀ ⊗ ⋯ ⊗ a_q)` to `b ⊗ (da₀ ∧ ⋯ ∧ da_q)` in `B
⊗[P] ⋀^(q+1)[P] Ω[P/k]`. -/
theorem higherProjection_tprod (q : ℕ) (P : Over B) (b : B) (a : Fin (q + 1) → P.left) :
    let X : ModuleCat.{max u v} k := (complex k B P).X (q + 1)
    let Y : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B (q + 1)).obj P
    let π : X ⟶ Y := higherProjection.{u, v} k B (q + 1) P
    let w : Y := CommAlgCat.cotangentHigherTensor.{u, v} k B q P b a
    π.hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) = w := by
  dsimp only
  let : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  let : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  let w : B ⊗[P.left] (⋀[P.left]^(q + 1) (KaehlerDifferential k P.left)) :=
    b ⊗ₜ[P.left] exteriorPower.ιMulti P.left (q + 1)
      (fun i => KaehlerDifferential.D k P.left (a i))
  have hπ : ((Symmetric.coefficientDifferentialFormChainMap k P.left B).f (q + 1)).hom
      (b ⊗ₜ[k] PiTensorProduct.tprod k a) = ULift.up w :=
    Symmetric.coefficientDifferentialFormChainMap_tprod k P.left B (q + 1) b a
  have hLift : (rawFormLevelIso.{u, v} k B (q + 1) P).hom.hom (ULift.up w) =
      CommAlgCat.cotangentHigherTensor.{u, v} k B q P b a :=
    rawFormLevelIso_succ_hom_apply k B q P w
  exact (higherProjection_apply k B (q + 1) P _).trans
    (follow_value (fun x => x) (rawFormLevelIso.{u, v} k B (q + 1) P).hom.hom
      _ (ULift.up w) _ hπ hLift)

/-- The regular-module formula for the weight-zero projection.

The degree-zero tensor with coefficient `b ∈ B` maps to the inverse regular-unitor image of
`b` in the weight-zero cotangent module `B ⊗[P] P`. -/
theorem higherProjection_zero (P : Over B) (b : B) (a : Fin 0 → P.left) :
    (higherProjection.{u, v} k B 0 P).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (CommAlgCat.cotangentWeightZeroLevelIso k B P).inv.hom b := by
  let : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  let : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  let w : B ⊗[P.left] (⋀[P.left]^0 (KaehlerDifferential k P.left)) :=
    b ⊗ₜ[P.left] exteriorPower.ιMulti P.left 0
      (fun i => KaehlerDifferential.D k P.left (a i))
  let e : (B ⊗[P.left] (⋀[P.left]^0 (KaehlerDifferential k P.left))) ≃ₗ[k] B :=
    ((TensorProduct.congr (LinearEquiv.refl P.left B)
      (exteriorPower.zeroEquiv P.left (KaehlerDifferential k P.left))).trans
        (TensorProduct.rid P.left B)).restrictScalars k
  have hπ : ((Symmetric.coefficientDifferentialFormChainMap k P.left B).f 0).hom
      (b ⊗ₜ[k] PiTensorProduct.tprod k a) = ULift.up w :=
    Symmetric.coefficientDifferentialFormChainMap_tprod k P.left B 0 b a
  have hUnit : e w = b := by
    change TensorProduct.rid P.left B
      ((TensorProduct.congr (LinearEquiv.refl P.left B)
        (exteriorPower.zeroEquiv P.left (KaehlerDifferential k P.left)))
          (b ⊗ₜ[P.left] exteriorPower.ιMulti P.left 0
            (fun i => KaehlerDifferential.D k P.left (a i)))) = b
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      exteriorPower.zeroEquiv_ιMulti, TensorProduct.rid_tmul, one_smul]
  have hLift : (rawFormLevelIso.{u, v} k B 0 P).hom.hom (ULift.up w) =
      (CommAlgCat.cotangentWeightZeroLevelIso k B P).inv.hom b :=
    (rawFormLevelIso_zero_hom_apply k B P w).trans
      (congrArg (CommAlgCat.cotangentWeightZeroLevelIso k B P).inv.hom hUnit)
  exact (higherProjection_apply k B 0 P _).trans
    (follow_value (fun x => x) (rawFormLevelIso.{u, v} k B 0 P).hom.hom
      _ (ULift.up w) _ hπ hLift)

/-- Naturality of the higher cotangent projection.

For `f : P → Q` over `B`, applying the Hochschild map and then projecting to higher cotangent
forms equals projecting first and applying the weight-`q` higher cotangent map restricted to
`k`. -/
theorem higherProjection_naturality {P Q : Over B} (f : P ⟶ Q) (q : ℕ) :
    let X : ModuleCat.{max u v} k := (complex k B P).X q
    let Y : ModuleCat.{max u v} k := (complex k B Q).X q
    let ZP : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B q).obj P
    let ZQ : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B q).obj Q
    let c : X ⟶ Y := (map k B f).f q
    let p : X ⟶ ZP := higherProjection.{u, v} k B q P
    let t : Y ⟶ ZQ := higherProjection.{u, v} k B q Q
    let h : ZP ⟶ ZQ := (ModuleCat.restrictScalars (algebraMap k B)).map
      (CommAlgCat.cotangentHigherMap.{u, v} k B q f)
    c ≫ t = p ≫ h := by
  dsimp only
  cases q with
  | zero =>
      let X : ModuleCat.{max u v} k := (complex k B P).X 0
      let Y : ModuleCat.{max u v} k := (complex k B Q).X 0
      let ZP : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B 0).obj P
      let ZQ : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B 0).obj Q
      let c : X ⟶ Y := (map k B f).f 0
      let p : X ⟶ ZP := higherProjection.{u, v} k B 0 P
      let t : Y ⟶ ZQ := higherProjection.{u, v} k B 0 Q
      let h : ZP ⟶ ZQ := (higherGroundFunctor.{u, v} k B 0).map f
      apply ModuleCat.hom_ext
      apply ModuleCat.Algebra.Hochschild.tensorPower_ext
        (k := k) (A := P.left) (M := B) (N := ZQ) (n := 0)
      intro b a
      let wP := CommAlgCat.cotangentWeightZeroLevelIso k B P
      let wQ := CommAlgCat.cotangentWeightZeroLevelIso k B Q
      have hTransport : CommAlgCat.cotangentHigherMap.{u, v} k B 0 f = wP.hom ≫ wQ.inv :=
        CommAlgCat.cotangentHigherMap_zero_eq_weightZero.{u, v} k B f
      have hMap : h.hom (wP.inv.hom b) = wQ.inv.hom b :=
        (higherGroundFunctor_map_apply k B f 0 (wP.inv.hom b)).trans
          ((module_eq_comp_value wP.hom wQ.inv hTransport (wP.inv.hom b)).trans
            (congrArg wQ.inv.hom (module_iso_hom_inv_value wP b)))
      let x : X := b ⊗ₜ[k] PiTensorProduct.tprod k a
      let y : Y := b ⊗ₜ[k] PiTensorProduct.tprod k (fun j => f.left.hom (a j))
      have hc : c.hom x = y := map_tprod k B f 0 b a
      have hp := higherProjection_zero k B P b a
      have ht := higherProjection_zero k B Q b (fun j => f.left.hom (a j))
      exact module_word_square c p t h x y (wP.inv.hom b) (wQ.inv.hom b) hc hp ht hMap
  | succ q =>
      let X : ModuleCat.{max u v} k := (complex k B P).X (q + 1)
      let Y : ModuleCat.{max u v} k := (complex k B Q).X (q + 1)
      let ZP : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B (q + 1)).obj P
      let ZQ : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B (q + 1)).obj Q
      let c : X ⟶ Y := (map k B f).f (q + 1)
      let p : X ⟶ ZP := higherProjection.{u, v} k B (q + 1) P
      let t : Y ⟶ ZQ := higherProjection.{u, v} k B (q + 1) Q
      let h : ZP ⟶ ZQ := (higherGroundFunctor.{u, v} k B (q + 1)).map f
      apply ModuleCat.hom_ext
      apply ModuleCat.Algebra.Hochschild.tensorPower_ext
        (k := k) (A := P.left) (M := B) (N := ZQ) (n := q + 1)
      intro b a
      let VP : ModuleCat.{max u v} B := CommAlgCat.cotangentHigherLevel.{u, v} k B (q + 1) P
      let VQ : ModuleCat.{max u v} B := CommAlgCat.cotangentHigherLevel.{u, v} k B (q + 1) Q
      let wP : VP := CommAlgCat.cotangentHigherTensor.{u, v} k B q P b a
      let wQ : VQ := CommAlgCat.cotangentHigherTensor.{u, v} k B q Q b (fun j => f.left.hom (a j))
      let fB : VP ⟶ VQ := CommAlgCat.cotangentHigherMap.{u, v} k B (q + 1) f
      have hB : fB.hom wP = wQ := CommAlgCat.cotangentHigherMap_tensor.{u, v} k B q f b a
      have hMap : h.hom (show ZP from wP) = (show ZQ from wQ) :=
        restricted_map_value_eq (X := VP) (Y := VQ) (algebraMap k B) fB wP wQ hB
      let x : X := b ⊗ₜ[k] PiTensorProduct.tprod k a
      let y : Y := b ⊗ₜ[k] PiTensorProduct.tprod k (fun j => f.left.hom (a j))
      have hc : c.hom x = y := map_tprod k B f (q + 1) b a
      have hp := higherProjection_tprod k B q P b a
      have ht := higherProjection_tprod k B q Q b (fun j => f.left.hom (a j))
      dsimp only at hp ht
      exact module_word_square c p t h x y (show ZP from wP) (show ZQ from wQ) hc hp ht hMap

/-- Postcomposition of higher cotangent projection naturality.

The naturality square for the weight-`q` projection remains commutative after composing both
routes with any ground-linear map from the target higher cotangent module. -/
theorem higherProjection_naturality_assoc {P Q : Over B} (f : P ⟶ Q) (q : ℕ)
    {M : ModuleCat.{max u v} k}
    (g : (higherGroundFunctor.{u, v} k B q).obj Q ⟶ M) :
    (map k B f).f q ≫ higherProjection.{u, v} k B q Q ≫ g =
      higherProjection.{u, v} k B q P ≫ (higherGroundFunctor.{u, v} k B q).map f ≫ g := by
  let c := (map k B f).f q
  let p : (complex k B P).X q ⟶
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.cotangentHigherLevel.{u, v} k B q P) := higherProjection.{u, v} k B q P
  let t : (complex k B Q).X q ⟶
      (ModuleCat.restrictScalars (algebraMap k B)).obj
        (CommAlgCat.cotangentHigherLevel.{u, v} k B q Q) := higherProjection.{u, v} k B q Q
  let h := (ModuleCat.restrictScalars (algebraMap k B)).map
    (CommAlgCat.cotangentHigherMap.{u, v} k B q f)
  have hn : c ≫ t = p ≫ h := higherProjection_naturality k B f q
  exact module_reassoc c t p h hn g

/-- Naturality of the lifted-form cotangent comparison.

The weight-`q` comparison from lifted coefficient forms to ground higher cotangent modules
commutes with the form map and the higher cotangent map induced by `f : P → Q` over `B`. -/
theorem rawFormLevelIso_naturality {P Q : Over B} (f : P ⟶ Q) (q : ℕ) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : Algebra Q.left B := CommAlgCat.cotangentAlgebra k B Q
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    letI : IsScalarTower k Q.left B := CommAlgCat.cotangentScalarTower k B Q
    let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q P
    let Y : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q Q
    let ZP : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B q).obj P
    let ZQ : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B q).obj Q
    let g : X ⟶ Y := rawFormMap k B f q
    let eP : X ⟶ ZP := (rawFormLevelIso.{u, v} k B q P).hom
    let eQ : Y ⟶ ZQ := (rawFormLevelIso.{u, v} k B q Q).hom
    let h : ZP ⟶ ZQ := (ModuleCat.restrictScalars (algebraMap k B)).map
      (CommAlgCat.cotangentHigherMap.{u, v} k B q f)
    g ≫ eQ = eP ≫ h := by
  dsimp only
  let : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  let : Algebra Q.left B := CommAlgCat.cotangentAlgebra k B Q
  let : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  let : IsScalarTower k Q.left B := CommAlgCat.cotangentScalarTower k B Q
  let KP := Symmetric.chainComplex k P.left B
  let KQ := Symmetric.chainComplex k Q.left B
  let FP := Symmetric.coefficientDifferentialFormComplex k P.left B
  let FQ := Symmetric.coefficientDifferentialFormComplex k Q.left B
  let XP : ModuleCat.{max u v} k := KP.X q
  let XQ : ModuleCat.{max u v} k := KQ.X q
  let TP : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q P
  let TQ : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q Q
  let YP : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B q).obj P
  let YQ : ModuleCat.{max u v} k := (higherGroundFunctor.{u, v} k B q).obj Q
  let : Module k XP := XP.isModule
  let : Module k XQ := XQ.isModule
  let : Module k TP := TP.isModule
  let : Module k TQ := TQ.isModule
  let : Module k YP := YP.isModule
  let : Module k YQ := YQ.isModule
  let πP : XP ⟶ TP := (Symmetric.coefficientDifferentialFormChainMap k P.left B).f q
  let πQ : XQ ⟶ TQ := (Symmetric.coefficientDifferentialFormChainMap k Q.left B).f q
  let g : TP ⟶ TQ := rawFormMap k B f q
  let eP : TP ⟶ YP := (rawFormLevelIso.{u, v} k B q P).hom
  let eQ : TQ ⟶ YQ := (rawFormLevelIso.{u, v} k B q Q).hom
  let c := (Symmetric.originalAlgebraCoefficientChainMap k f.left.hom
    (LinearMap.id : B →ₗ[k] B) (coefficientCompatibility k B f)).f q
  let h : YP ⟶ YQ := (ModuleCat.restrictScalars (algebraMap k B)).map
    (CommAlgCat.cotangentHigherMap.{u, v} k B q f)
  have hSquare (z : XP) : πQ.hom (c.hom z) = g.hom (πP.hom z) :=
    congrArg (fun t => (t.f q).hom z)
      (Symmetric.coefficientDifferentialFormChainMap_algebra k f.left.hom
        (LinearMap.id : B →ₗ[k] B) (coefficientCompatibility k B f))
  have hHigher (z : XP) : eQ.hom (πQ.hom (c.hom z)) = h.hom (eP.hom (πP.hom z)) := by
    have hn : (higherProjection.{u, v} k B q Q).hom (c.hom z) =
        h.hom ((higherProjection.{u, v} k B q P).hom z) :=
      congrArg (fun t => t.hom z) (higherProjection_naturality k B f q)
    exact (higherProjection_apply k B q Q (c.hom z)).symm.trans
      (hn.trans (congrArg h.hom (higherProjection_apply k B q P z)))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := Symmetric.coefficientDifferentialFormChainMap_surjective k P.left B q x
  exact (congrArg eQ.hom (hSquare z)).symm.trans (hHigher z)

/-- Postcomposition of lifted-form comparison naturality.

The naturality square of the lifted-form comparison remains commutative after any ground-
linear map from the target higher cotangent module. -/
theorem rawFormLevelIso_naturality_assoc {P Q : Over B} (f : P ⟶ Q) (q : ℕ)
    {M : ModuleCat.{max u v} k}
    (t : (higherGroundFunctor.{u, v} k B q).obj Q ⟶ M) :
    letI : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
    letI : Algebra Q.left B := CommAlgCat.cotangentAlgebra k B Q
    letI : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
    letI : IsScalarTower k Q.left B := CommAlgCat.cotangentScalarTower k B Q
    rawFormMap k B f q ≫ (rawFormLevelIso.{u, v} k B q Q).hom ≫ t =
      (rawFormLevelIso.{u, v} k B q P).hom ≫ (higherGroundFunctor.{u, v} k B q).map f ≫ t := by
  let : Algebra P.left B := CommAlgCat.cotangentAlgebra k B P
  let : Algebra Q.left B := CommAlgCat.cotangentAlgebra k B Q
  let : IsScalarTower k P.left B := CommAlgCat.cotangentScalarTower k B P
  let : IsScalarTower k Q.left B := CommAlgCat.cotangentScalarTower k B Q
  let X : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q P
  let Y : ModuleCat.{max u v} k := rawFormLevel.{u, v} k B q Q
  let ZP : ModuleCat.{max u v} k := (ModuleCat.restrictScalars (algebraMap k B)).obj
    (CommAlgCat.cotangentHigherLevel.{u, v} k B q P)
  let ZQ : ModuleCat.{max u v} k := (ModuleCat.restrictScalars (algebraMap k B)).obj
    (CommAlgCat.cotangentHigherLevel.{u, v} k B q Q)
  let g : X ⟶ Y := rawFormMap k B f q
  let eP : X ⟶ ZP := (rawFormLevelIso.{u, v} k B q P).hom
  let eQ : Y ⟶ ZQ := (rawFormLevelIso.{u, v} k B q Q).hom
  let h : ZP ⟶ ZQ := (ModuleCat.restrictScalars (algebraMap k B)).map
    (CommAlgCat.cotangentHigherMap.{u, v} k B q f)
  have hn : g ≫ eQ = eP ≫ h := rawFormLevelIso_naturality k B f q
  exact module_reassoc g eQ eP h hn t

end ModuleCat.Algebra.Hochschild.Symmetric.AugmentedAlgebra
