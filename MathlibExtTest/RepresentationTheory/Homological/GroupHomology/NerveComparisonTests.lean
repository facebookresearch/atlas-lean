/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.Homological.GroupHomology.NerveComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.NativeCoverHomologyOne
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

/-- The endpoint is Mathlib's actual native H2, with the original trivial
representation, for an arbitrary group and coefficient ring in the shared universe. -/
example (k G : Type u) [CommRing k] [Group G] :
    groupHomology (Rep.trivial k G k) 2 ≅
      (CategoryTheory.nerve (SingleObj G)).homology
        (ModuleCat.of k k : ModuleCat.{u} k) 2 :=
  groupHomology.trivialNerveHomologyIso k G 2

/-- The original degree-two bar generator has literal inverse successive
arrows in the direct one-object nerve. -/
example (k G : Type u) [CommRing k] [Group G] (g : Fin 2 → G) :
    ModuleCat.ofHom (Finsupp.lsingle g (R := k) (M := k)) ≫
        (groupHomology.trivialNerveChainIso k G).hom.f 2 =
      (CategoryTheory.nerve (SingleObj G)).ιChainComplex
        (R := (ModuleCat.of k k : ModuleCat.{u} k))
        ((CategoryTheory.nerve.singleObjEquiv G 2).symm (fun i => (g i)⁻¹)) :=
  groupHomology.trivialNerveChainIso_generator k G 2 g

/-- Native group H2 maps retain the original group homomorphism under the
canonical nerve comparison. -/
example (k G H : Type u) [CommRing k] [Group G] [Group H] (f : G →* H) :
    groupHomology.map f
        (𝟙 (Rep.trivial k G k) : Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k H k)) 2 ≫
        (groupHomology.trivialNerveHomologyIso k H 2).hom =
      (groupHomology.trivialNerveHomologyIso k G 2).hom ≫
        SSet.homologyMap (CategoryTheory.nerveMap (SingleObj.mapHom _ _ f))
          (ModuleCat.of k k : ModuleCat.{u} k) 2 :=
  groupHomology.trivialNerveHomologyIso_hom_naturality k G f 2

/-- The public inverse component law recovers the actual original degree-two
bar generator without unfolding the comparison implementation. -/
example (k G : Type u) [CommRing k] [Group G] (g : Fin 2 → G) :
    (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).ιChainComplex
        (R := (ModuleCat.of k k : ModuleCat.{u} k))
        ((CategoryTheory.nerve.singleObjOppEquiv G 2).symm g) ≫
      (groupHomology.trivialOppositeNerveChainIso k G).inv.f 2 =
        ModuleCat.ofHom (Finsupp.lsingle g (R := k) (M := k)) := by
  rw [groupHomology.trivialOppositeNerveChainIso_inv_f]
  exact groupHomology.trivialOppositeNerveChainObjIso_inv_generator k G 2 g

/-- The public forward component law reads the actual original degree-two
bar generator without unfolding the comparison implementation. -/
example (k G : Type u) [CommRing k] [Group G] (g : Fin 2 → G) :
    ModuleCat.ofHom (Finsupp.lsingle g (R := k) (M := k)) ≫
        (groupHomology.trivialOppositeNerveChainIso k G).hom.f 2 =
      (CategoryTheory.nerve (SingleObj Gᵐᵒᵖ)).ιChainComplex
        (R := (ModuleCat.of k k : ModuleCat.{u} k))
        ((CategoryTheory.nerve.singleObjOppEquiv G 2).symm g) := by
  rw [groupHomology.trivialOppositeNerveChainIso_hom_f]
  exact groupHomology.trivialOppositeNerveChainObjIso_generator k G 2 g

/-- Both original simplex dictionaries remain available directly to clients. -/
example (G : Type u) [Group G] (g : Fin 2 → G) :
    (CategoryTheory.nerve.inversionIso G).inv.app (Opposite.op ⦋2⦌)
        ((CategoryTheory.nerve.singleObjEquiv G 2).symm g) =
      (CategoryTheory.nerve.singleObjOppEquiv G 2).symm (fun i => (g i)⁻¹) :=
  CategoryTheory.nerve.inversionIso_inv_simplex G 2 g

/-- The original native fundamental-groupoid endomorphism group is an actual
large-universe integral H2 client. No vanishing or group-comparison premise is used. -/
example (X : SSet.{u}) (x : X _⦋0⦌) :
    groupHomology (Rep.trivial (ULift.{u} ℤ)
      (End (SSet.FundamentalGroupoid.mk x)) (ULift.{u} ℤ)) 2 ≅
      (CategoryTheory.nerve (SingleObj (End (SSet.FundamentalGroupoid.mk x)))).homology
        (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ) : ModuleCat.{u} (ULift.{u} ℤ)) 2 :=
  groupHomology.trivialNerveHomologyIso _ _ 2

/-- The same actual native cover supplies its canonical connected H0
augmentation and integral H1 zero for the later coefficient-row construction. -/
example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    IsIso ((SSet.KanComplex.nativeCover X x).homology₀ε
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) ∧
    IsZero ((SSet.KanComplex.nativeCover X x).homology
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 1) := by
  let _ : (SSet.KanComplex.nativeCover X x).IsConnected :=
    SSet.KanComplex.nativeCover_isConnected (X := X) (x := x)
  exact ⟨inferInstance, SSet.KanComplex.nativeCoverHomologyOne_isZero X x⟩

end
