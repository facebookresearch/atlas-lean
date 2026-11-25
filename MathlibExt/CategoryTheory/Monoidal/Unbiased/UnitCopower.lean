/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Types.Basic

/-!
# UnitCopower

Copowers of the tensor unit and their functorial finite tensor comparisons.
-/

/- Source proof segment: FiniteTensorUnitScalars -/
section source_FiniteTensorUnitScalars
/-!
# The tensor of finite families of the actual empty tensor

The empty tensor is not assumed terminal. Its finite multiplication
is the actual flatten comparison at a family of empty families.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory FiniteFamily

private theorem scalarPostSquare {V : Type*} [Category* V]
    {X Y A B Z : V} (i : X ⟶ Y) (q : Y ⟶ B) (p : X ⟶ A)
    (f : A ⟶ B) (r : B ⟶ Z) (s : A ⟶ Z)
    (hn : i ≫ q = p ≫ f) (hf : f ≫ r = s) :
    i ≫ (q ≫ r) = p ≫ s := by
  rw [← Category.assoc i q, hn, Category.assoc p f, hf]

variable {C : Type u} [Category.{v} C] [FiniteTensor C]

/-- The actual unbiased tensor unit is the tensor of the empty family. -/
def unitObject (C : Type u) [Category.{v} C] [FiniteTensor C] : C :=
  (FiniteTensor.tensor (V := C)).obj FiniteFamily.empty

/-- A finite family of empty families, on the original finite index. -/
def emptyScalarBlocks (I : FintypeCat.{0}) : FiniteFamily (FiniteFamily C) :=
  ⟨I, fun _ => FiniteFamily.empty⟩

/-- The actual finite family of empty tensors on the original index. -/
def emptyScalarFamily (I : FintypeCat.{0}) : FiniteFamily C :=
  (FiniteFamily.map (FiniteTensor.tensor (V := C))).obj (emptyScalarBlocks I)

/-- Flattening a family of empty families retains no inputs. -/
def emptyScalarFlattenIso (I : FintypeCat.{0}) :
    (FiniteFamily.flatten (C := C)).obj (emptyScalarBlocks I) ≅ FiniteFamily.empty := by
  let : IsEmpty ((FiniteFamily.flatten (C := C)).obj (emptyScalarBlocks I)).index :=
    ⟨fun p => nomatch p.2⟩
  let : IsEmpty (FiniteFamily.empty (C := C)).index := ⟨fun p => nomatch p⟩
  exact FiniteFamily.isoOfReindex (Equiv.equivOfIsEmpty _ _) (fun p => nomatch p.2)

/-- The actual tensor of a finite family of units is the unit,
through the original empty-family flattening isomorphism. -/
def emptyScalarTensorIso (I : FintypeCat.{0}) :
    (FiniteTensor.tensor (V := C)).obj (emptyScalarFamily I) ≅ unitObject C :=
  (FiniteTensor.flattenIso.app (emptyScalarBlocks I)).symm ≪≫
    (FiniteTensor.tensor (V := C)).mapIso (emptyScalarFlattenIso I)

/-- Relabel all original empty blocks by the supplied bijection. -/
def emptyScalarBlocksRelabel {I J : FintypeCat.{0}} (e : I ≃ J) :
    emptyScalarBlocks (C := C) I ⟶ emptyScalarBlocks J where
  equiv := e
  hom _ := 𝟙 FiniteFamily.empty

/-- Relabel the finite family of units using identity components. -/
def emptyScalarFamilyRelabel {I J : FintypeCat.{0}} (e : I ≃ J) :
    emptyScalarFamily (C := C) I ⟶ emptyScalarFamily J where
  equiv := e
  hom _ := 𝟙 (unitObject C)

/-- Tensoring the relabelled empty block maps gives precisely
the supplied original relabelling and identity unit components. -/
theorem emptyScalarBlocksRelabel_map {I J : FintypeCat.{0}} (e : I ≃ J) :
    (FiniteFamily.map (FiniteTensor.tensor (V := C))).map (emptyScalarBlocksRelabel e) =
      emptyScalarFamilyRelabel e := by
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    exact heq_of_eq ((FiniteTensor.tensor (V := C)).map_id FiniteFamily.empty)

omit [FiniteTensor C] in
/-- The original empty-profile quotient is unchanged by every
finite input relabelling, including the empty input bijection. -/
theorem emptyScalarFlattenIso_relabel {I J : FintypeCat.{0}} (e : I ≃ J) :
    (FiniteFamily.flatten (C := C)).map (emptyScalarBlocksRelabel e) ≫
        (emptyScalarFlattenIso J).hom = (emptyScalarFlattenIso I).hom := by
  apply FiniteFamily.Hom_ext
  · ext p
    exact nomatch p.2
  · intro p
    exact nomatch p.2

/-- The finite multiplication of the actual empty tensor is
natural under every supplied finite index permutation. -/
theorem emptyScalarTensorIso_relabel {I J : FintypeCat.{0}} (e : I ≃ J) :
    (FiniteTensor.tensor (V := C)).map (emptyScalarFamilyRelabel e) ≫
        (emptyScalarTensorIso J).hom = (emptyScalarTensorIso I).hom := by
  let T := FiniteTensor.tensor (V := C)
  have hn := (FiniteTensor.flattenIso (V := C)).inv.naturality (emptyScalarBlocksRelabel e)
  have hmap := congrArg T.map (emptyScalarBlocksRelabel_map (C := C) e)
  have hf := congrArg T.map (emptyScalarFlattenIso_relabel (C := C) e)
  have hs : T.map (emptyScalarFamilyRelabel e) ≫
      (FiniteTensor.flattenIso (V := C)).inv.app (emptyScalarBlocks J) =
    (FiniteTensor.flattenIso (V := C)).inv.app (emptyScalarBlocks I) ≫
      T.map ((FiniteFamily.flatten (C := C)).map (emptyScalarBlocksRelabel e)) :=
    (congrArg (fun k => k ≫ (FiniteTensor.flattenIso (V := C)).inv.app (emptyScalarBlocks J))
      hmap.symm).trans hn
  exact scalarPostSquare (T.map (emptyScalarFamilyRelabel e))
    ((FiniteTensor.flattenIso (V := C)).inv.app (emptyScalarBlocks J))
    ((FiniteTensor.flattenIso (V := C)).inv.app (emptyScalarBlocks I))
    (T.map ((FiniteFamily.flatten (C := C)).map (emptyScalarBlocksRelabel e)))
    (T.map (emptyScalarFlattenIso J).hom) (T.map (emptyScalarFlattenIso I).hom)
    hs ((T.map_comp _ _).symm.trans hf)




end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_FiniteTensorUnitScalars

/- Source proof segment: UnitCopowerFunctor -/
section source_UnitCopowerFunctor
/-!
# The actual unit-copower coefficient functor
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe us v u

namespace CategoryTheory.FiniteTensor.UnitCopower

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C] [FiniteTensor C] [HasColimitsOfSize.{us, us} C]

/-- The actual coproduct of copies of the tensor unit indexed by
the supplied source type. Every source map relabels those copies. -/
def functor : Type us ⥤ C where
  obj X := ∐ (fun _ : X => unitObject C)
  map f := Sigma.map' f (fun _ => 𝟙 (unitObject C))
  map_id X := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_comp_map', Category.id_comp, Category.comp_id]
    rfl
  map_comp f g := by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_comp_map', Category.id_comp,
      Sigma.ι_comp_map'_assoc]
    rfl

/-- Its actual object is the ordinary source-sized unit copower. -/
@[simp]
theorem functor_obj (X : Type us) :
    (functor C).obj X = ∐ (fun _ : X => unitObject C) := rfl

/-- The coefficient map acts on each original coproduct injection
by the supplied map of source indices. -/
@[reassoc (attr := simp)]
theorem ι_map {X Y : Type us} (f : X ⟶ Y) (x : X) :
    Sigma.ι (fun _ : X => unitObject C) x ≫ (functor C).map f =
      Sigma.ι (fun _ : Y => unitObject C) (f x) := by
  with_unfolding_all
    change Sigma.ι (fun _ : X => unitObject C) x ≫
        Sigma.map' (g := fun _ : X => unitObject C) (f := fun _ : Y => unitObject C)
          f (fun _ => 𝟙 (unitObject C)) = _
    exact (Sigma.ι_comp_map' (g := fun _ : X => unitObject C)
      (f := fun _ : Y => unitObject C) f (fun _ => 𝟙 (unitObject C)) x).trans (Category.id_comp _)



end CategoryTheory.FiniteTensor.UnitCopower
end
end
end source_UnitCopowerFunctor
