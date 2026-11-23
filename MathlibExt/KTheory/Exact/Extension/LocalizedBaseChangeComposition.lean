/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.LocalizedBaseChange

/-!
# Composition of the original localized base changes

The pullback functor for `f ≫ g` is naturally isomorphic to pullback along `g` followed by
pullback along `f`. Its components compare the actual chosen Cartesian domains in the
literal fibers. Naturality follows from the original full lift-factor equations and
Cartesian uniqueness, retaining the original total arrows and all denominators.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicKTheory.LocalizedBaseChange

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- Chosen pullback composition is a natural isomorphism in the actual localized fibers.
The order is contravariant: first pull back along `g`, then along `f`. -/
def baseChangeCompositionNatIso {R S T : QuillenQ C} (f : R ⟶ S) (g : S ⟶ T) :
    baseChangeFunctor (f ≫ g) ≅ baseChangeFunctor g ⋙ baseChangeFunctor f := by
  let component (a : Functor.Fiber (projection (C := C)) T) :
      baseChangeObject (f ≫ g) a ≅ baseChangeObject f (baseChangeObject g a) := by
    let e : (baseChangeObject (f ≫ g) a).val ≅
        (baseChangeObject f (baseChangeObject g a)).val :=
      Functor.IsFibered.pullbackPullbackIso (p := projection (C := C)) a.property g f
    let _ : Functor.IsCartesian (projection (C := C)) f
        (baseChangeLift f (baseChangeObject g a)) := by
      change Functor.IsCartesian (projection (C := C)) f
        (Functor.IsPreFibered.pullbackMap (p := projection (C := C))
          (baseChangeObject g a).property f)
      infer_instance
    let _ : Functor.IsCartesian (projection (C := C)) g (baseChangeLift g a) := by
      change Functor.IsCartesian (projection (C := C)) g
        (Functor.IsPreFibered.pullbackMap (p := projection (C := C)) a.property g)
      infer_instance
    let _ : Functor.IsCartesian (projection (C := C)) (f ≫ g)
        (baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a) :=
      Functor.IsFibered.comp f g
        (baseChangeLift f (baseChangeObject g a)) (baseChangeLift g a)
    let _ : Functor.IsCartesian (projection (C := C)) (f ≫ g)
        (baseChangeLift (f ≫ g) a) := by
      change Functor.IsCartesian (projection (C := C)) (f ≫ g)
        (Functor.IsPreFibered.pullbackMap (p := projection (C := C)) a.property (f ≫ g))
      infer_instance
    have hHom : Functor.IsHomLift (projection (C := C)) (𝟙 R) e.hom := by
      dsimp only [e, Functor.IsFibered.pullbackPullbackIso]
      exact Functor.IsCartesian.domainUniqueUpToIso_inv_isHomLift (R := R)
        (projection (C := C)) (f ≫ g)
        (baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a)
        (baseChangeLift (f ≫ g) a)
    have hInv : Functor.IsHomLift (projection (C := C)) (𝟙 R) e.inv := by
      dsimp only [e, Functor.IsFibered.pullbackPullbackIso]
      exact Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift (R := R)
        (projection (C := C)) (f ≫ g)
        (baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a)
        (baseChangeLift (f ≫ g) a)
    refine
      { hom := ⟨e.hom, hHom⟩
        inv := ⟨e.inv, hInv⟩
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply Functor.Fiber.hom_ext
      exact e.hom_inv_id
    · apply Functor.Fiber.hom_ext
      exact e.inv_hom_id
  have component_fac (a : Functor.Fiber (projection (C := C)) T) :
      (component a).hom.val ≫
          (baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a) =
        baseChangeLift (f ≫ g) a := by
    let l := baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a
    have hF : Functor.IsCartesian (projection (C := C)) f
        (baseChangeLift f (baseChangeObject g a)) := by
      change Functor.IsCartesian (projection (C := C)) f
        (Functor.IsPreFibered.pullbackMap (p := projection (C := C))
          (baseChangeObject g a).property f)
      infer_instance
    have hG : Functor.IsCartesian (projection (C := C)) g (baseChangeLift g a) := by
      change Functor.IsCartesian (projection (C := C)) g
        (Functor.IsPreFibered.pullbackMap (p := projection (C := C)) a.property g)
      infer_instance
    let _ : Functor.IsCartesian (projection (C := C)) f
        (baseChangeLift f (baseChangeObject g a)) := hF
    let _ : Functor.IsCartesian (projection (C := C)) g (baseChangeLift g a) := hG
    have hCart : Functor.IsCartesian (projection (C := C)) (f ≫ g) l :=
      Functor.IsFibered.comp f g
        (baseChangeLift f (baseChangeObject g a)) (baseChangeLift g a)
    have hDirectCart : Functor.IsCartesian (projection (C := C)) (f ≫ g)
        (baseChangeLift (f ≫ g) a) := by
      change Functor.IsCartesian (projection (C := C)) (f ≫ g)
        (Functor.IsPreFibered.pullbackMap (p := projection (C := C)) a.property (f ≫ g))
      infer_instance
    have hDirect : Functor.IsHomLift (projection (C := C)) (f ≫ g)
        (baseChangeLift (f ≫ g) a) := hDirectCart.toIsHomLift
    change (@Functor.IsCartesian.map _ _ _ _ (projection (C := C)) _ _ _ _ (f ≫ g)
        l hCart _ (baseChangeLift (f ≫ g) a) hDirect) ≫ l = baseChangeLift (f ≫ g) a
    exact @Functor.IsCartesian.fac _ _ _ _ (projection (C := C)) _ _ _ _ (f ≫ g)
      l hCart _ (baseChangeLift (f ≫ g) a) hDirect
  refine NatIso.ofComponents component ?_
  intro a b phi
  let left : baseChangeObject (f ≫ g) a ⟶ baseChangeObject f (baseChangeObject g b) :=
    baseChangeMap (f ≫ g) phi ≫ (component b).hom
  let right : baseChangeObject (f ≫ g) a ⟶ baseChangeObject f (baseChangeObject g b) :=
    (component a).hom ≫ baseChangeMap f (baseChangeMap g phi)
  apply Functor.Fiber.hom_ext
  change left.val = right.val
  let l := baseChangeLift f (baseChangeObject g b) ≫ baseChangeLift g b
  have hF : Functor.IsCartesian (projection (C := C)) f
      (baseChangeLift f (baseChangeObject g b)) := by
    change Functor.IsCartesian (projection (C := C)) f
      (Functor.IsPreFibered.pullbackMap (p := projection (C := C))
        (baseChangeObject g b).property f)
    infer_instance
  have hG : Functor.IsCartesian (projection (C := C)) g (baseChangeLift g b) := by
    change Functor.IsCartesian (projection (C := C)) g
      (Functor.IsPreFibered.pullbackMap (p := projection (C := C)) b.property g)
    infer_instance
  let _ : Functor.IsCartesian (projection (C := C)) f
      (baseChangeLift f (baseChangeObject g b)) := hF
  let _ : Functor.IsCartesian (projection (C := C)) g (baseChangeLift g b) := hG
  let _ : Functor.IsCartesian (projection (C := C)) (f ≫ g) l :=
    Functor.IsFibered.comp f g
      (baseChangeLift f (baseChangeObject g b)) (baseChangeLift g b)
  let _ : Functor.IsHomLift (projection (C := C)) (𝟙 R) left.val := left.property
  let _ : Functor.IsHomLift (projection (C := C)) (𝟙 R) right.val := right.property
  apply Functor.IsCartesian.ext (projection (C := C)) (f ≫ g) l left.val right.val
  have hLeft : left.val ≫ l = baseChangeLift (f ≫ g) a ≫ phi.val := by
    change ((baseChangeMap (f ≫ g) phi).val ≫ (component b).hom.val) ≫ l = _
    calc
      ((baseChangeMap (f ≫ g) phi).val ≫ (component b).hom.val) ≫ l =
          (baseChangeMap (f ≫ g) phi).val ≫ ((component b).hom.val ≫ l) :=
        Category.assoc _ _ _
      _ = (baseChangeMap (f ≫ g) phi).val ≫ baseChangeLift (f ≫ g) b :=
        congrArg (fun q => (baseChangeMap (f ≫ g) phi).val ≫ q) (component_fac b)
      _ = baseChangeLift (f ≫ g) a ≫ phi.val := baseChangeMap_fac (f ≫ g) phi
  have hNested : (baseChangeMap f (baseChangeMap g phi)).val ≫ l =
      (baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a) ≫ phi.val := by
    change (baseChangeMap f (baseChangeMap g phi)).val ≫
        (baseChangeLift f (baseChangeObject g b) ≫ baseChangeLift g b) = _
    calc
      (baseChangeMap f (baseChangeMap g phi)).val ≫
          (baseChangeLift f (baseChangeObject g b) ≫ baseChangeLift g b) =
        ((baseChangeMap f (baseChangeMap g phi)).val ≫
          baseChangeLift f (baseChangeObject g b)) ≫ baseChangeLift g b :=
        (Category.assoc _ _ _).symm
      _ = (baseChangeLift f (baseChangeObject g a) ≫ (baseChangeMap g phi).val) ≫
          baseChangeLift g b :=
        congrArg (fun q => q ≫ baseChangeLift g b)
          (baseChangeMap_fac f (baseChangeMap g phi))
      _ = baseChangeLift f (baseChangeObject g a) ≫
          ((baseChangeMap g phi).val ≫ baseChangeLift g b) := Category.assoc _ _ _
      _ = baseChangeLift f (baseChangeObject g a) ≫ (baseChangeLift g a ≫ phi.val) :=
        congrArg (fun q => baseChangeLift f (baseChangeObject g a) ≫ q)
          (baseChangeMap_fac g phi)
      _ = (baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a) ≫ phi.val :=
        (Category.assoc _ _ _).symm
  have hRight : right.val ≫ l = baseChangeLift (f ≫ g) a ≫ phi.val := by
    change ((component a).hom.val ≫ (baseChangeMap f (baseChangeMap g phi)).val) ≫ l = _
    calc
      ((component a).hom.val ≫ (baseChangeMap f (baseChangeMap g phi)).val) ≫ l =
          (component a).hom.val ≫ ((baseChangeMap f (baseChangeMap g phi)).val ≫ l) :=
        Category.assoc _ _ _
      _ = (component a).hom.val ≫
          ((baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a) ≫ phi.val) :=
        congrArg (fun q => (component a).hom.val ≫ q) hNested
      _ = ((component a).hom.val ≫
          (baseChangeLift f (baseChangeObject g a) ≫ baseChangeLift g a)) ≫ phi.val :=
        (Category.assoc _ _ _).symm
      _ = baseChangeLift (f ≫ g) a ≫ phi.val :=
        congrArg (fun q => q ≫ phi.val) (component_fac a)
  exact hLeft.trans hRight.symm

/-- The component uses the stock comparison of the original direct and iterated chosen lifts. -/
theorem baseChangeCompositionNatIso_hom_val {R S T : QuillenQ C}
    (f : R ⟶ S) (g : S ⟶ T) (a : Functor.Fiber (projection (C := C)) T) :
    ((baseChangeCompositionNatIso f g).hom.app a).val =
      (Functor.IsFibered.pullbackPullbackIso (p := projection (C := C)) a.property g f).hom :=
  rfl

/-- The inverse component is the original comparison in the reverse domain direction. -/
theorem baseChangeCompositionNatIso_inv_val {R S T : QuillenQ C}
    (f : R ⟶ S) (g : S ⟶ T) (a : Functor.Fiber (projection (C := C)) T) :
    ((baseChangeCompositionNatIso f g).inv.app a).val =
      (Functor.IsFibered.pullbackPullbackIso (p := projection (C := C)) a.property g f).inv :=
  rfl

end AlgebraicKTheory.LocalizedBaseChange

end
