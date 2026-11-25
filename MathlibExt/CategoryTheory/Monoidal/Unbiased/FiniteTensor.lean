/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteFamily
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.Category

@[expose] public section

namespace CategoryTheory.FiniteFamily

universe v u
variable {C : Type u} [Category.{v} C]

/-- Functor `FiniteFamily C ⥤ FiniteFamily C` via `map singleton ⋙ flatten`. -/
def mapSingletonFlatten : FiniteFamily C ⥤ FiniteFamily C :=
  FiniteFamily.map (FiniteFamily.singleton (C := C)) ⋙ FiniteFamily.flatten

/-- Functor `FiniteFamily C ⥤ FiniteFamily C` via `singleton ⋙ flatten`. -/
def singletonFlatten : FiniteFamily C ⥤ FiniteFamily C :=
  (FiniteFamily.singleton (C := FiniteFamily C)) ⋙ FiniteFamily.flatten

/-- Functor `map flatten ⋙ flatten` on triple families. -/
def mapFlattenFlatten : FiniteFamily (FiniteFamily (FiniteFamily C)) ⥤ FiniteFamily C :=
  FiniteFamily.map (FiniteFamily.flatten (C := C)) ⋙ FiniteFamily.flatten

/-- Functor `flatten ⋙ flatten` on triple families. -/
def flattenFlatten : FiniteFamily (FiniteFamily (FiniteFamily C)) ⥤ FiniteFamily C :=
  FiniteFamily.flatten (C := FiniteFamily C) ⋙ FiniteFamily.flatten

/-- Component morphism for `mapSingletonFlatten`. -/
def mapSingletonFlattenHom (X : FiniteFamily C) :
    Hom ((mapSingletonFlatten (C := C)).obj X) X where
  equiv := Equiv.sigmaPUnit X.index
  hom := fun _ => 𝟙 _

/-- Inverse component for `mapSingletonFlatten`. -/
def mapSingletonFlattenInv (X : FiniteFamily C) :
    Hom X ((mapSingletonFlatten (C := C)).obj X) where
  equiv := (Equiv.sigmaPUnit X.index).symm
  hom := fun _ => 𝟙 _

/-- Pointwise isomorphism for `mapSingletonFlatten`. -/
def mapSingletonFlattenIsoApp (X : FiniteFamily C) :
    (mapSingletonFlatten (C := C)).obj X ≅ X where
  hom := mapSingletonFlattenHom X
  inv := mapSingletonFlattenInv X
  hom_inv_id := by
    apply Hom_ext
    · exact Equiv.self_trans_symm _
    · intro x
      exact heq_of_eq
        ((show (Hom.comp (mapSingletonFlattenHom X)
          (mapSingletonFlattenInv X)).hom x =
          𝟙 ((mapSingletonFlatten.obj X).obj x) ≫
          𝟙 (X.obj ((mapSingletonFlattenHom X).equiv x)) from rfl).trans
          (Category.comp_id _))
  inv_hom_id := by
    apply Hom_ext
    · exact Equiv.symm_trans_self _
    · intro x
      exact heq_of_eq
        ((show (Hom.comp (mapSingletonFlattenInv X)
          (mapSingletonFlattenHom X)).hom x =
          𝟙 (X.obj x) ≫
          𝟙 ((mapSingletonFlatten.obj X).obj
            ((mapSingletonFlattenInv X).equiv x)) from rfl).trans
          (Category.comp_id _))

/-- Natural isomorphism `mapSingletonFlatten ≅ 𝟭`. -/
def mapSingletonFlattenIso :
    (mapSingletonFlatten (C := C) : FiniteFamily C ⥤ FiniteFamily C) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => mapSingletonFlattenIsoApp X) (by
    intro X Y f
    apply Hom_ext
    · ext x
      cases x with
      | mk i u =>
        cases u with
        | unit => rfl
    · intro x
      cases x with
      | mk i u =>
        cases u with
        | unit =>
          have h1 :
            (Hom.comp (mapSingletonFlatten.map f)
              (mapSingletonFlattenHom Y)).hom
              ⟨i, PUnit.unit⟩ =
            f.hom i ≫ 𝟙 _ := rfl
          have h2 :
            (Hom.comp (mapSingletonFlattenHom X) f).hom
              ⟨i, PUnit.unit⟩ =
            𝟙 _ ≫ f.hom i := rfl
          have h3 : f.hom i ≫ (𝟙 _ : _ ⟶ _) = f.hom i := by simp
          have h4 : (𝟙 _ : _ ⟶ _) ≫ f.hom i = f.hom i := by simp
          exact heq_of_eq
            (h1.trans (h3.trans (h4.symm.trans h2.symm)))
  )

/-- Component morphism for `singletonFlatten`. -/
def singletonFlattenHom (X : FiniteFamily C) :
    Hom ((singletonFlatten (C := C)).obj X) X where
  equiv := (Equiv.sigmaEquivProd PUnit X.index).trans (Equiv.punitProd X.index)
  hom := fun _ => 𝟙 _

/-- Inverse component for `singletonFlatten`. -/
def singletonFlattenInv (X : FiniteFamily C) :
    Hom X ((singletonFlatten (C := C)).obj X) where
  equiv := ((Equiv.sigmaEquivProd PUnit X.index).trans (Equiv.punitProd X.index)).symm
  hom := fun _ => 𝟙 _

/-- Pointwise isomorphism for `singletonFlatten`. -/
def singletonFlattenIsoApp (X : FiniteFamily C) :
    (singletonFlatten (C := C)).obj X ≅ X where
  hom := singletonFlattenHom X
  inv := singletonFlattenInv X
  hom_inv_id := by
    apply Hom_ext
    · exact Equiv.self_trans_symm _
    · intro x
      exact heq_of_eq
        ((show (Hom.comp (singletonFlattenHom X)
          (singletonFlattenInv X)).hom x =
          𝟙 ((singletonFlatten.obj X).obj x) ≫
          𝟙 (X.obj ((singletonFlattenHom X).equiv x)) from rfl).trans
          (Category.comp_id _))
  inv_hom_id := by
    apply Hom_ext
    · exact Equiv.symm_trans_self _
    · intro x
      exact heq_of_eq
        ((show (Hom.comp (singletonFlattenInv X)
          (singletonFlattenHom X)).hom x =
          𝟙 (X.obj x) ≫
          𝟙 ((singletonFlatten.obj X).obj
            ((singletonFlattenInv X).equiv x)) from rfl).trans
          (Category.comp_id _))

/-- Natural isomorphism `singletonFlatten ≅ 𝟭`. -/
def singletonFlattenIso :
    (singletonFlatten (C := C) : FiniteFamily C ⥤ FiniteFamily C) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => singletonFlattenIsoApp X) (by
    intro X Y f
    apply Hom_ext
    · ext x
      cases x with
      | mk pu i =>
        cases pu with
        | unit => rfl
    · intro x
      cases x with
      | mk pu i =>
        cases pu with
        | unit =>
          have h1 :
            (Hom.comp (singletonFlatten.map f)
              (singletonFlattenHom Y)).hom
              ⟨PUnit.unit, i⟩ =
            f.hom i ≫ 𝟙 _ := rfl
          have h2 :
            (Hom.comp (singletonFlattenHom X) f).hom
              ⟨PUnit.unit, i⟩ =
            𝟙 _ ≫ f.hom i := rfl
          have h3 : f.hom i ≫ (𝟙 _ : _ ⟶ _) = f.hom i := by simp
          have h4 : (𝟙 _ : _ ⟶ _) ≫ f.hom i = f.hom i := by simp
          exact heq_of_eq
            (h1.trans (h3.trans (h4.symm.trans h2.symm)))
  )

/-- Component morphism for flatten associativity. -/
def flattenAssocHom (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Hom ((mapFlattenFlatten (C := C)).obj X) ((flattenFlatten (C := C)).obj X) where
  equiv := (Equiv.sigmaAssoc (fun a b => ((X.obj a).obj b).index)).symm
  hom := fun _ => 𝟙 _

/-- Inverse component for flatten associativity. -/
def flattenAssocInv (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    Hom ((flattenFlatten (C := C)).obj X) ((mapFlattenFlatten (C := C)).obj X) where
  equiv := Equiv.sigmaAssoc (fun a b => ((X.obj a).obj b).index)
  hom := fun _ => 𝟙 _

/-- Pointwise isomorphism for flatten associativity. -/
def flattenAssocIsoApp (X : FiniteFamily (FiniteFamily (FiniteFamily C))) :
    (mapFlattenFlatten (C := C)).obj X ≅ (flattenFlatten (C := C)).obj X where
  hom := flattenAssocHom X
  inv := flattenAssocInv X
  hom_inv_id := by
    apply Hom_ext
    · exact Equiv.symm_trans_self _
    · intro x
      exact heq_of_eq
        ((show (Hom.comp (flattenAssocHom X)
          (flattenAssocInv X)).hom x =
          𝟙 ((mapFlattenFlatten.obj X).obj x) ≫
          𝟙 ((flattenFlatten.obj X).obj
            ((flattenAssocHom X).equiv x)) from rfl).trans
          (Category.comp_id _))
  inv_hom_id := by
    apply Hom_ext
    · exact Equiv.self_trans_symm _
    · intro x
      exact heq_of_eq
        ((show (Hom.comp (flattenAssocInv X)
          (flattenAssocHom X)).hom x =
          𝟙 ((flattenFlatten.obj X).obj x) ≫
          𝟙 ((mapFlattenFlatten.obj X).obj
            ((flattenAssocInv X).equiv x)) from rfl).trans
          (Category.comp_id _))

/-- Natural isomorphism `mapFlattenFlatten ≅ flattenFlatten`. -/
def flattenAssocIso :
    (mapFlattenFlatten (C := C) : FiniteFamily (FiniteFamily (FiniteFamily C)) ⥤ FiniteFamily C) ≅
    (flattenFlatten (C := C) : _ ⥤ _) :=
  NatIso.ofComponents (fun X => flattenAssocIsoApp X) (by
    intro X Y f
    apply Hom_ext
    · ext x
      cases x with
      | mk a bc =>
        cases bc with
        | mk b c => rfl
    · intro x
      cases x with
      | mk a bc =>
        cases bc with
        | mk b c =>
          have h1 :
            (Hom.comp (mapFlattenFlatten.map f)
              (flattenAssocHom Y)).hom ⟨a, ⟨b, c⟩⟩ =
            ((f.hom a).hom b).hom c ≫ 𝟙 _ := rfl
          have h2 :
            (Hom.comp (flattenAssocHom X)
              (flattenFlatten.map f)).hom ⟨a, ⟨b, c⟩⟩ =
            𝟙 _ ≫ ((f.hom a).hom b).hom c := rfl
          have h3 :
            ((f.hom a).hom b).hom c ≫ (𝟙 _ : _ ⟶ _) =
            ((f.hom a).hom b).hom c := by simp
          have h4 :
            (𝟙 _ : _ ⟶ _) ≫ ((f.hom a).hom b).hom c =
            ((f.hom a).hom b).hom c := by simp
          exact heq_of_eq
            (h1.trans (h3.trans (h4.symm.trans h2.symm)))
  )

universe v₁ u₁ v₂ u₂

/-- Strict equality `singleton ⋙ map F = F ⋙ singleton` as a natural iso.

This localizes the definitional equality of the singleton and map
operations; it is `Iso.refl` because the two functors are definitionally equal. -/
def singletonMapIso {C₁ : Type u₁} {D : Type u₂}
    [Category.{v₁} C₁] [Category.{v₂} D] (F : C₁ ⥤ D) :
    (FiniteFamily.singleton (C := C₁) ⋙ FiniteFamily.map F) ≅
      (F ⋙ FiniteFamily.singleton (C := D)) :=
  Iso.refl _

/-- Strict equality `flatten ⋙ map F = map (map F) ⋙ flatten` as a natural iso.

This localizes the definitional equality of flatten and map; it is
`Iso.refl` because the two functors are definitionally equal. -/
def flattenMapIso {C₁ : Type u₁} {D : Type u₂}
    [Category.{v₁} C₁] [Category.{v₂} D] (F : C₁ ⥤ D) :
    (FiniteFamily.flatten (C := C₁) ⋙ FiniteFamily.map F) ≅
      (FiniteFamily.map (FiniteFamily.map F) ⋙ FiniteFamily.flatten (C := D)) :=
  Iso.refl _

/-- Lifts an isomorphism of functors through `FiniteFamily.map`.

For `α : F ≅ G`, this is the induced iso `map F ≅ map G`. -/
def mapIso {C₁ : Type u₁} {D : Type u₂} [Category.{v₁} C₁] [Category.{v₂} D]
    {F G : C₁ ⥤ D} (α : F ≅ G) : FiniteFamily.map F ≅ FiniteFamily.map G :=
  (FiniteFamily.mapFunctor (C₁ := C₁) (D := D)).mapIso α

end CategoryTheory.FiniteFamily

namespace CategoryTheory

universe v u

/-- Coherent unbiased finite tensor on `V`: pseudoalgebra for the finite-family monad. -/
class FiniteTensor (V : Type u) [Category.{v} V] where
  /-- Unbiased tensor product `FiniteFamily V ⥤ V`. -/
  tensor : FiniteFamily V ⥤ V
  /-- Unit: singleton then tensor is isomorphic to the identity. -/
  singletonIso : FiniteFamily.singleton (C := V) ⋙ tensor ≅ 𝟭 V
  /-- Multiplication: flatten then tensor is isomorphic to map tensor then tensor. -/
  flattenIso : FiniteFamily.flatten (C := V) ⋙ tensor ≅ FiniteFamily.map tensor ⋙ tensor
  /-- Left unit law corresponding to `singletonFlattenIso`. -/
  singletonFlattenLaw :
    Functor.isoWhiskerRight FiniteFamily.singletonFlattenIso tensor ≪≫
      Functor.leftUnitor tensor =
      Functor.isoWhiskerLeft (FiniteFamily.singleton (C := FiniteFamily V)) flattenIso ≪≫
        Functor.isoWhiskerRight (FiniteFamily.singletonMapIso tensor) tensor ≪≫
        Functor.isoWhiskerLeft tensor singletonIso ≪≫
        Functor.rightUnitor tensor
  /-- Right unit law corresponding to `mapSingletonFlattenIso`. -/
  mapSingletonFlattenLaw :
    Functor.isoWhiskerRight FiniteFamily.mapSingletonFlattenIso tensor ≪≫
      Functor.leftUnitor tensor =
      Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.singleton (C := V))) flattenIso ≪≫
        Functor.isoWhiskerRight (FiniteFamily.mapIso singletonIso) tensor ≪≫
        Functor.leftUnitor tensor
  /-- Associativity / pentagon law corresponding to `flattenAssocIso`. -/
  flattenAssocLaw :
    Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.flatten (C := V))) flattenIso ≪≫
      Functor.isoWhiskerRight (FiniteFamily.mapIso flattenIso) tensor =
      Functor.isoWhiskerRight FiniteFamily.flattenAssocIso tensor ≪≫
        Functor.isoWhiskerLeft (FiniteFamily.flatten (C := FiniteFamily V)) flattenIso ≪≫
        Functor.isoWhiskerRight (FiniteFamily.flattenMapIso tensor) tensor ≪≫
        Functor.isoWhiskerLeft (FiniteFamily.map (FiniteFamily.map tensor)) flattenIso

variable {V : Type u} [Category.{v} V] [FiniteTensor V]

/-- The flatten-iso interchange law for fibered flat maps (`hom`
direction): if a flat map `G` on flattened families equals
`flatten.map F` for a nested map `F`, then pushing `G` through
`flattenIso.hom` is `flattenIso` naturality at `F`. Every interchange
instance of this shape hence reduces to exhibiting the fiber data. -/
theorem flattenIso_push_fibered {N M : FiniteFamily (FiniteFamily V)}
    (F : N ⟶ M)
    (G : (FiniteFamily.flatten (C := V)).obj N ⟶
      (FiniteFamily.flatten (C := V)).obj M)
    (h : G = (FiniteFamily.flatten (C := V)).map F) :
    (FiniteTensor.tensor (V := V)).map G ≫
        (FiniteTensor.flattenIso (V := V)).hom.app M =
      (FiniteTensor.flattenIso (V := V)).hom.app N ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map F) := by
  have hnat := (FiniteTensor.flattenIso (V := V)).hom.naturality F
  have hG : (FiniteTensor.tensor (V := V)).map G =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map F) :=
    congrArg _ h
  have hL : (FiniteTensor.tensor (V := V)).map G ≫
          (FiniteTensor.flattenIso (V := V)).hom.app M =
        (FiniteTensor.tensor (V := V)).map
            ((FiniteFamily.flatten (C := V)).map F) ≫
          (FiniteTensor.flattenIso (V := V)).hom.app M :=
    congrArg (· ≫ (FiniteTensor.flattenIso (V := V)).hom.app M) hG
  exact hL.trans hnat

/-- The flatten-iso interchange law for fibered flat maps (`inv`
direction): if `G` equals `flatten.map F`, then `flattenIso.inv`
slides past `G` by naturality of the inverse. -/
theorem flattenIso_inv_push_fibered {N M : FiniteFamily (FiniteFamily V)}
    (F : M ⟶ N)
    (G : (FiniteFamily.flatten (C := V)).obj M ⟶
      (FiniteFamily.flatten (C := V)).obj N)
    (h : G = (FiniteFamily.flatten (C := V)).map F) :
    (FiniteTensor.flattenIso (V := V)).inv.app M ≫
        (FiniteTensor.tensor (V := V)).map G =
      (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map F) ≫
        (FiniteTensor.flattenIso (V := V)).inv.app N := by
  have hnat := (FiniteTensor.flattenIso (V := V)).inv.naturality F
  have hG : (FiniteTensor.tensor (V := V)).map G =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.flatten (C := V)).map F) :=
    congrArg _ h
  have hL : (FiniteTensor.flattenIso (V := V)).inv.app M ≫
          (FiniteTensor.tensor (V := V)).map G =
        (FiniteTensor.flattenIso (V := V)).inv.app M ≫
          (FiniteTensor.tensor (V := V)).map
            ((FiniteFamily.flatten (C := V)).map F) :=
    congrArg ((FiniteTensor.flattenIso (V := V)).inv.app M ≫ ·) hG
  exact hL.trans hnat.symm

omit [FiniteTensor V] in
/-- Fiber criterion for flattened nested maps: a flat map `G` equals
`flatten.map F` when its reindexing is fibered over `F.equiv` with
matching fiber equivalences and its components match fiberwise. This
turns each concrete interchange obligation into fiber computations. -/
theorem flatMap_eq_flattenMap_of_fibered
    {N M : FiniteFamily (FiniteFamily V)} (F : N ⟶ M)
    (G : (FiniteFamily.flatten (C := V)).obj N ⟶
      (FiniteFamily.flatten (C := V)).obj M)
    (he : ∀ (a : N.index) (b : (N.obj a).index),
      G.equiv ⟨a, b⟩ = ⟨F.equiv a, (F.hom a).equiv b⟩)
    (hh : ∀ (a : N.index) (b : (N.obj a).index),
      HEq (G.hom ⟨a, b⟩) ((F.hom a).hom b)) :
    G = (FiniteFamily.flatten (C := V)).map F := by
  apply FiniteFamily.Hom_ext
  · apply Equiv.ext
    intro p
    obtain ⟨a, b⟩ := p
    have hp := he a b
    have hr : ((FiniteFamily.flatten (C := V)).map F).equiv
        ⟨a, b⟩ = ⟨F.equiv a, (F.hom a).equiv b⟩ := rfl
    exact hp.trans hr.symm
  · intro p
    obtain ⟨a, b⟩ := p
    have hp := hh a b
    have hr : ((FiniteFamily.flatten (C := V)).map F).hom
        ⟨a, b⟩ = (F.hom a).hom b := rfl
    exact hp.trans (heq_of_eq hr.symm)

/-- Combined fibered push: a flat map satisfying the fiber criterion
pushes through `flattenIso.hom` to the mapped nested map. -/
theorem flattenIso_push_of_fibered
    {N M : FiniteFamily (FiniteFamily V)} (F : N ⟶ M)
    (G : (FiniteFamily.flatten (C := V)).obj N ⟶
      (FiniteFamily.flatten (C := V)).obj M)
    (he : ∀ (a : N.index) (b : (N.obj a).index),
      G.equiv ⟨a, b⟩ = ⟨F.equiv a, (F.hom a).equiv b⟩)
    (hh : ∀ (a : N.index) (b : (N.obj a).index),
      HEq (G.hom ⟨a, b⟩) ((F.hom a).hom b)) :
    (FiniteTensor.tensor (V := V)).map G ≫
        (FiniteTensor.flattenIso (V := V)).hom.app M =
      (FiniteTensor.flattenIso (V := V)).hom.app N ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.map (FiniteTensor.tensor (V := V))).map F) := by
  have hG : G = (FiniteFamily.flatten (C := V)).map F :=
    flatMap_eq_flattenMap_of_fibered F G he hh
  exact flattenIso_push_fibered F G hG

/-- Singleton rebracketing around a mapped singleton hom collapses to
the hom: push the map through `singletonIso.hom` by naturality, then
cancel the iso. -/
theorem FiniteTensor.singletonIso_inv_map_hom {X Y : V} (f : X ⟶ Y) :
    (FiniteTensor.singletonIso (V := V)).inv.app X ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f) ≫
        (FiniteTensor.singletonIso (V := V)).hom.app Y =
      f := by
  have hnat := (FiniteTensor.singletonIso (V := V)).hom.naturality f
  have hnat' : (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.singleton (C := V)).map f) ≫
        (FiniteTensor.singletonIso (V := V)).hom.app Y =
      (FiniteTensor.singletonIso (V := V)).hom.app X ≫ f :=
    hnat
  have hIso : (FiniteTensor.singletonIso (V := V)).inv.app X ≫
        (FiniteTensor.singletonIso (V := V)).hom.app X =
      𝟙 _ :=
    Iso.inv_hom_id_app _ _
  calc (FiniteTensor.singletonIso (V := V)).inv.app X ≫
            (FiniteTensor.tensor (V := V)).map
              ((FiniteFamily.singleton (C := V)).map f) ≫
            (FiniteTensor.singletonIso (V := V)).hom.app Y
        = (FiniteTensor.singletonIso (V := V)).inv.app X ≫
            ((FiniteTensor.singletonIso (V := V)).hom.app X ≫ f) :=
          congrArg _ hnat'
      _ = ((FiniteTensor.singletonIso (V := V)).inv.app X ≫
            (FiniteTensor.singletonIso (V := V)).hom.app X) ≫ f :=
          (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ f := congrArg (· ≫ f) hIso
      _ = f := Category.id_comp _

/-- The `flattenAssocLaw` pseudoalgebra law at a triple-nested
family: the two iterated-flatten composites agree as morphisms. -/
theorem FiniteTensor.flattenAssocLaw_app
    (N : FiniteFamily (FiniteFamily (FiniteFamily V))) :
    (Functor.isoWhiskerLeft
          (FiniteFamily.map (FiniteFamily.flatten (C := V)))
          (FiniteTensor.flattenIso (V := V)) ≪≫
        Functor.isoWhiskerRight
          (FiniteFamily.mapIso (FiniteTensor.flattenIso (V := V)))
          (FiniteTensor.tensor (V := V))).hom.app N =
      (Functor.isoWhiskerRight FiniteFamily.flattenAssocIso
          (FiniteTensor.tensor (V := V)) ≪≫
        Functor.isoWhiskerLeft
          (FiniteFamily.flatten (C := FiniteFamily V))
          (FiniteTensor.flattenIso (V := V)) ≪≫
        Functor.isoWhiskerRight
          (FiniteFamily.flattenMapIso (FiniteTensor.tensor (V := V)))
          (FiniteTensor.tensor (V := V)) ≪≫
        Functor.isoWhiskerLeft
          (FiniteFamily.map
            (FiniteFamily.map (FiniteTensor.tensor (V := V))))
          (FiniteTensor.flattenIso (V := V))).hom.app N := by
  exact congrArg (fun I => I.hom.app N)
    (FiniteTensor.flattenAssocLaw (V := V))

/-- Whisker-level unfolding of the `flattenAssocLaw` app equation:
each whiskered iso acts by its components. -/
theorem FiniteTensor.flattenAssocLaw_app_unfold
    (N : FiniteFamily (FiniteFamily (FiniteFamily V))) :
    (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map (FiniteFamily.flatten (C := V))).obj N) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIso
            (FiniteTensor.flattenIso (V := V))).hom.app N) =
      (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flattenAssocIso (C := V)).hom.app N) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.flatten (C := FiniteFamily V)).obj N) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.flattenMapIso
            (FiniteTensor.tensor (V := V))).hom.app N) ≫
        (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map
            (FiniteFamily.map
              (FiniteTensor.tensor (V := V)))).obj N) := by
  exact FiniteTensor.flattenAssocLaw_app N

universe uW vW

omit [FiniteTensor V] in
/-- The flatten/map interchange iso is the identity: flattening
then mapping equals mapping twice then flattening on the nose.
Universe-polymorphic in the target, matching `flattenMapIso`. -/
theorem FiniteTensor.flattenMapIso_hom_app_eq_id
    {W : Type uW} [Category.{vW} W] (F : V ⥤ W)
    (X : FiniteFamily (FiniteFamily V)) :
    (FiniteFamily.flattenMapIso F).hom.app X = 𝟙 _ := rfl

/-- The collapse iso reindexes trivially. -/
@[simp]
theorem mapIso_singletonIso_hom_equiv (X : FiniteFamily V) :
    ((FiniteFamily.mapIso
      (FiniteTensor.singletonIso (V := V))).hom.app X).equiv =
      Equiv.refl X.index := rfl

/-- The collapse iso acts by singleton collapse in each fiber. -/
@[simp]
theorem mapIso_singletonIso_hom_hom (X : FiniteFamily V)
    (i : X.index) :
    ((FiniteFamily.mapIso
      (FiniteTensor.singletonIso (V := V))).hom.app X).hom i =
      (FiniteTensor.singletonIso (V := V)).hom.app (X.obj i) := rfl

/-- Left unit law in firing form: pushing the singleton-flatten
identification through the tensor is the flatten identification at
the singleton family followed by singleton collapse. This is
`singletonFlattenLaw` at components, with the strict
`singletonMapIso` and unitor factors reduced. -/
theorem singletonFlattenLaw_app (N : FiniteFamily V) :
    (FiniteTensor.tensor (V := V)).map
        (FiniteFamily.singletonFlattenIso.hom.app N) =
      (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.singleton
            (C := FiniteFamily V)).obj N) ≫
        (FiniteTensor.singletonIso (V := V)).hom.app
          ((FiniteTensor.tensor (V := V)).obj N) := by
  have h2 := congrArg Iso.hom
    (FiniteTensor.singletonFlattenLaw (V := V))
  have h := congrArg (fun η => η.app N) h2
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app] at h
  have hw : (FiniteFamily.singletonMapIso
      (FiniteTensor.tensor (V := V))).hom.app N = 𝟙 _ := rfl
  have hmap : (FiniteTensor.tensor (V := V)).map
      ((FiniteFamily.singletonMapIso
        (FiniteTensor.tensor (V := V))).hom.app N) = 𝟙 _ := by
    rw [hw]
    exact (FiniteTensor.tensor (V := V)).map_id _
  rw [hmap] at h
  have eR : (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.singleton
            (C := FiniteFamily V)).obj N) ≫
        𝟙 _ ≫ (FiniteTensor.singletonIso (V := V)).hom.app
          ((FiniteTensor.tensor (V := V)).obj N) ≫ 𝟙 _ =
      (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.singleton
            (C := FiniteFamily V)).obj N) ≫
        (FiniteTensor.singletonIso (V := V)).hom.app
          ((FiniteTensor.tensor (V := V)).obj N) :=
    ((congrArg ((FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.singleton
            (C := FiniteFamily V)).obj N) ≫ ·)
        (Category.id_comp _)).trans
      (congrArg ((FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.singleton
            (C := FiniteFamily V)).obj N) ≫ ·)
        (Category.comp_id _)))
  exact (Category.comp_id _).symm.trans (h.trans eR)

/-- Right unit law in firing form: pushing the map-singleton-flatten
identification through the tensor is the flatten identification at
the mapped singleton family followed by the tensor of the collapse
iso. This is `mapSingletonFlattenLaw` at components, with the
unitor factors reduced. -/
theorem mapSingletonFlattenLaw_app (X : FiniteFamily V) :
    (FiniteTensor.tensor (V := V)).map
        (FiniteFamily.mapSingletonFlattenIso.hom.app X) =
      (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map
            (FiniteFamily.singleton (C := V))).obj X) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIso
            (FiniteTensor.singletonIso (V := V))).hom.app X) := by
  have h2 := congrArg Iso.hom
    (FiniteTensor.mapSingletonFlattenLaw (V := V))
  have h := congrArg (fun η => η.app X) h2
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  have hmid : (Functor.isoWhiskerRight
          (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := V)))
          (FiniteTensor.tensor (V := V)) ≪≫
        (FiniteTensor.tensor (V := V)).leftUnitor).hom.app X =
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIso
            (FiniteTensor.singletonIso (V := V))).hom.app X) ≫
          (FiniteTensor.tensor (V := V)).leftUnitor.hom.app X := rfl
  have hC : (FiniteTensor.tensor (V := V)).leftUnitor.hom.app X =
      𝟙 ((FiniteTensor.tensor (V := V)).obj X) :=
    Functor.leftUnitor_hom_app _ _
  have h2nd : (Functor.isoWhiskerRight
          (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := V)))
          (FiniteTensor.tensor (V := V)) ≪≫
        (FiniteTensor.tensor (V := V)).leftUnitor).hom.app X =
      (FiniteTensor.tensor (V := V)).map
        ((FiniteFamily.mapIso
          (FiniteTensor.singletonIso (V := V))).hom.app X) :=
    (hmid.trans (congrArg ((FiniteTensor.tensor (V := V)).map
      ((FiniteFamily.mapIso
        (FiniteTensor.singletonIso (V := V))).hom.app X) ≫ ·) hC)).trans
      (Category.comp_id _)
  have eR : (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map
            (FiniteFamily.singleton (C := V))).obj X) ≫
        (Functor.isoWhiskerRight
          (FiniteFamily.mapIso (FiniteTensor.singletonIso (V := V)))
          (FiniteTensor.tensor (V := V)) ≪≫
        (FiniteTensor.tensor (V := V)).leftUnitor).hom.app X =
      (FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map
            (FiniteFamily.singleton (C := V))).obj X) ≫
        (FiniteTensor.tensor (V := V)).map
          ((FiniteFamily.mapIso
            (FiniteTensor.singletonIso (V := V))).hom.app X) :=
    congrArg ((FiniteTensor.flattenIso (V := V)).hom.app
          ((FiniteFamily.map
            (FiniteFamily.singleton (C := V))).obj X) ≫ ·) h2nd
  exact (Category.comp_id _).symm.trans (h.trans eR)

end CategoryTheory
