/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativePrismaticSite
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Actual base and formal-geometry maps of relative prism sites

A base map is an actual delta-prism map and a map of the actual nilpotent
formal diagrams, with its structural square. The associated site functor
composes those two fixed maps. It retains the same prism rings and
completely-flat cover test; the coefficient comparison uses literal
scalar restriction along the specified base map.

This original adapter supplies the object/map boundary for the canonical
functoriality and base-change enhancements in Bhatt--Scholze,
arXiv:1905.08229v4, Theorem1.8. It does not assert a derived algebra
comparison or an arbitrary base-change isomorphism.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps

open CategoryTheory
open MathlibExt.RingTheory.BoundedPrisms
open PadicFormalSchemes RelativePrismaticSite

variable (p : ℕ) [Fact p.Prime] (P Q : Prism.{0} p)
variable (X : FormalScheme p P.ring P.ideal)
  (Y : FormalScheme p Q.ring Q.ideal)

/-- The actual base and geometric morphism, with its fixed structural square. -/
structure Map where
  base : P ⟶ Q
  geometry : Y.diagram ⟶ X.diagram
  square : geometry ≫ X.structureMap =
    Y.structureMap ≫ mapDiagram p base.hom base.ideal

/-- The actual identity base/formal morphism. -/
def Map.id : Map p P P X X where
  base := 𝟙 P
  geometry := 𝟙 X.diagram
  square := by
    change (𝟙 X.diagram) ≫ X.structureMap =
      X.structureMap ≫ mapDiagram p (RingHom.id P.ring) _
    rw [mapDiagram_id]
    simp

/-- Compose the actual prism map and the actual formal point. -/
def Map.object (f : Map p P Q X Y) (U : Obj p Q Y) : Obj p P X where
  prism := U.prism
  base := f.base ≫ U.base
  point := U.point ≫ f.geometry
  point_base := by
    rw [Category.assoc, f.square, ← Category.assoc, U.point_base]
    change mapDiagram p U.base.hom _ ≫ mapDiagram p f.base.hom _ =
      mapDiagram p (U.base.hom.comp f.base.hom) _
    exact (mapDiagram_comp p f.base.hom U.base.hom
      f.base.ideal U.base.ideal)

/-- The same actual ring map, with composed geometric/base equations. -/
def Map.morphism (f : Map p P Q X Y) {U V : Obj p Q Y}
    (g : U ⟶ V) : f.object p P Q X Y U ⟶ f.object p P Q X Y V where
  map := g.map
  base := by
    change (f.base ≫ V.base) ≫ g.map = f.base ≫ U.base
    rw [Category.assoc, g.base]
  point := by
    change mapDiagram p g.map.hom g.map.ideal ≫ (V.point ≫ f.geometry) =
      U.point ≫ f.geometry
    rw [← Category.assoc, g.point]

/-- The concrete site functor; no freely chosen inverse-image operator. -/
def Map.functor (f : Map p P Q X Y) : Obj p Q Y ⥤ Obj p P X where
  obj := f.object p P Q X Y
  map := f.morphism p P Q X Y
  map_id _ := by apply RelativePrismaticSite.Hom.ext; rfl
  map_comp _ _ := by apply RelativePrismaticSite.Hom.ext; rfl

/-- The complete-flat Tor/quotient cover test is literally unchanged. -/
theorem Map.cover_iff (f : Map p P Q X Y) {U V : Obj p Q Y} (g : U ⟶ V) :
    IsCover p P X ((f.functor p P Q X Y).map g) ↔ IsCover p Q Y g := Iff.rfl

/-- The specified scalar restriction, on the actual base-ring modules. -/
abbrev Map.restrictScalars (f : Map p P Q X Y) :=
  ModuleCat.restrictScalars.{1, 0, 0} f.base.hom

/-- The coefficient comparison retains every actual structural ring element. -/
def Map.coefficientIso (f : Map p P Q X Y) :
    (f.functor p P Q X Y).op ⋙ structurePresheaf p P X ≅
      structurePresheaf p Q Y ⋙ f.restrictScalars p P Q X Y :=
  NatIso.ofComponents (fun U ↦
    { hom := ConcreteCategory.ofHom (C := ModuleCat.{1} P.ring)
        { toFun x := x
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      inv := ConcreteCategory.ofHom (C := ModuleCat.{1} P.ring)
        { toFun x := x
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      hom_inv_id := by ext a; rfl
      inv_hom_id := by ext a; rfl }) (by
        intro U V g
        apply ModuleCat.hom_ext
        ext a
        rfl)

/-- Continuity of the functor of relative prismatic sites induced by a base map $f$ (a map of
prisms $P \to Q$ with a compatible map of formal schemes $Y \to X$, for a prime $p$): an instance
asserts that `f.functor`, from the relative prismatic site of $Y$ over $Q$ to that of $X$ over $P$,
is continuous for the topologies of the two sites. -/
class HasReindex (f : Map p P Q X Y) : Prop where
  continuous : Functor.IsContinuous (f.functor p P Q X Y)
    (topology p Q Y) (topology p P X)

attribute [instance] HasReindex.continuous

/-- Actual reindexing of base-module sheaves along the fixed site map. -/
def Map.sheafReindex (f : Map p P Q X Y) [HasReindex p P Q X Y f] :
    Sheaf (topology p P X) (ModuleCat.{1} P.ring) ⥤
      Sheaf (topology p Q Y) (ModuleCat.{1} P.ring) :=
  (f.functor p P Q X Y).sheafPushforwardContinuous (ModuleCat.{1} P.ring)
    (topology p Q Y) (topology p P X)

end MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps
