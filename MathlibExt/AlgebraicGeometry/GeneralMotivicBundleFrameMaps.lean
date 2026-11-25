/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicBundleModels
public import MathlibExt.AlgebraicGeometry.PointedMotivicQuotientMaps
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Native framed bundle and Thom maps

The total-space map is represented by the image of the original universal
section under the original module morphism. A frame gives actual global
coordinate functions by the native free-sheaf projections. Its affine map
is the literal Spec map of polynomial evaluation on those coordinates.
Complement and Thom maps retain that same whole scheme map.

Source: Voevodsky, arXiv:math/0107109v1, Sections 4 and 5. The section
representing convention is Spec Sym of the dual module, as recorded in
GeneralModuleTotalSpaces. Native free-sheaf and pullback maps are Mathlib.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralMotivicBundleFrameMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes MotivicBundleModels GeneralModuleTotalSpaces
open PointedMotivicModels PointedMotivicQuotients PointedMotivicQuotientMaps

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

/-- The original universal section expressed on the chosen smooth total space. -/
def smoothUniversal {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d) :
    Γ((Scheme.Modules.pullback G.projection.left).obj M, ⊤) :=
  pulledSection M G.total.projection G.total.universalSection
    G.projection.left G.totalIso.hom rfl

/-- Native coordinate projection of the free module sheaf. -/
def freeCoordinate (X : Scheme.{0}) (d : ℕ) (i : Fin d) :
    SheafOfModules.free (R := X.ringCatSheaf) (Fin d) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.freeHomEquiv (SheafOfModules.unit X.ringCatSheaf)).symm
    (fun j ↦ (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
      (if j = i then 𝟙 _ else 0))

/-- The coordinate is actual pulled frame projection applied to the universal section. -/
def frameCoordinate {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d))
    (i : Fin d) : Γ(G.smoothTotal.scheme.left, ⊤) :=
  ((((Scheme.Modules.pullback G.projection.left).map
      (φ.hom ≫ freeCoordinate X.scheme.left d i) ≫
    (AlgebraicBundleGeometry.pullbackUnit G.smoothTotal.scheme.left
      X.scheme.left G.projection.left).hom).val.app (op ⊤)).hom
        (smoothUniversal G))

/-- Actual polynomial evaluation of all frame coordinates. -/
def framePolynomial {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d)) :
    affineRing k d →+* Γ(G.smoothTotal.scheme.left, ⊤) :=
  MvPolynomial.eval₂Hom (GenericSectionMaps.scalarMap G.smoothTotal.scheme)
    (frameCoordinate G φ)

/-- The raw whole scheme map is fixed by native global sections and Spec. -/
def frameSchemeMap {P : SmoothProductSystem k} (A : StandardSchemes P)
    {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d)) :
    G.smoothTotal.scheme.left ⟶ (A.affine d).scheme.left :=
  G.smoothTotal.scheme.left.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (framePolynomial G φ)) ≫ (A.affineIso d).inv

omit [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] in
/-- Native polynomial coefficients retain the original field structure map. -/
theorem scalarMap_recovers (X : Over (Spec (.of k))) :
    X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (GenericSectionMaps.scalarMap X)) =
      X.hom := by
  change X.left.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) = _
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Only the base equation is needed to bundle that prescribed map over the field. -/
structure FrameOver {P : SmoothProductSystem k} (A : StandardSchemes P)
    {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d)) : Prop where
  over : frameSchemeMap A G φ ≫ (A.affine d).scheme.hom = G.smoothTotal.scheme.hom

/-- The base equation follows from the actual polynomial coefficient map. -/
theorem nativeFrameOver {P : SmoothProductSystem k} (A : StandardSchemes P)
    {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d)) :
    FrameOver A G φ where
  over := by
    rw [A.affine_base]
    simp only [frameSchemeMap, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom (algebraMap k (affineRing k d)) ≫
        CommRingCat.ofHom (framePolynomial G φ) =
        CommRingCat.ofHom (GenericSectionMaps.scalarMap G.smoothTotal.scheme) := by
      ext x
      simp [framePolynomial, MvPolynomial.algebraMap_eq]
    rw [h]
    exact scalarMap_recovers G.smoothTotal.scheme

/-- The native affine map, with its proved original field structure equation. -/
def frameMap {P : SmoothProductSystem k} (A : StandardSchemes P)
    {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d))
    (h : FrameOver A G φ) : G.smoothTotal ⟶ A.affine d :=
  Over.homMk (frameSchemeMap A G φ) h.over

/-- A frame carries the actual nonzero complement to the affine nonzero complement. -/
structure FrameComplementMap {P : SmoothProductSystem k} (A : StandardSchemes P)
    {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d)) where
  map : G.complement ⟶ A.complement d
  square : G.complementInclusion ≫ frameMap A G φ (nativeFrameOver A G φ) =
    map ≫ A.complementInclusion d

/-- The framed Thom map is the native quotient map of the actual coordinate square. -/
def frameThomMap {P : SmoothProductSystem k} (A : StandardSchemes P)
    {X : SmoothScheme k} {M : X.scheme.left.Modules} {d : ℕ}
    (G : BundleGeometry X M d)
    (φ : M ≅ SheafOfModules.free (R := X.scheme.left.ringCatSheaf) (Fin d))
    (C : FrameComplementMap A G φ) : G.thom ⟶ affineThomSphere A d :=
  cofiberMap (representedMap G.complementInclusion)
    (representedMap (A.complementInclusion d)) (representedMap C.map)
    (representedMap (frameMap A G φ (nativeFrameOver A G φ))) (by
      rw [← representedMap_comp, ← representedMap_comp, C.square])

/-- The module morphism determines the actual total-space section map. -/
def moduleTotalMap {X Y : SmoothScheme k}
    {M : X.scheme.left.Modules} {N : Y.scheme.left.Modules} {d e : ℕ}
    (G : BundleGeometry X M d) (H : BundleGeometry Y N e)
    (f : X ⟶ Y) (a : M ⟶ (Scheme.Modules.pullback f.left).obj N) :
    G.total.total ⟶ H.total.total :=
  H.total.lift (G.total.projection ≫ f.left)
    ((((Scheme.Modules.pullback G.total.projection).map a ≫
      (Scheme.Modules.pullbackComp G.total.projection f.left).hom.app N).val.app
        (op ⊤)).hom G.total.universalSection)

omit [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] in
/-- The total map lies over the same original scheme map. -/
theorem moduleTotalMap_over {X Y : SmoothScheme k}
    {M : X.scheme.left.Modules} {N : Y.scheme.left.Modules} {d e : ℕ}
    (G : BundleGeometry X M d) (H : BundleGeometry Y N e)
    (f : X ⟶ Y) (a : M ⟶ (Scheme.Modules.pullback f.left).obj N) :
    moduleTotalMap G H f a ≫ H.total.projection = G.total.projection ≫ f.left :=
  H.total.lift_over _ _

/-- Transport to the actual smooth presentations uses only their original isomorphisms. -/
def moduleSmoothMap {X Y : SmoothScheme k}
    {M : X.scheme.left.Modules} {N : Y.scheme.left.Modules} {d e : ℕ}
    (G : BundleGeometry X M d) (H : BundleGeometry Y N e)
    (f : X ⟶ Y) (a : M ⟶ (Scheme.Modules.pullback f.left).obj N) :
    G.smoothTotal ⟶ H.smoothTotal :=
  Over.homMk (G.totalIso.hom ≫ moduleTotalMap G H f a ≫ H.totalIso.inv) (by
    rw [H.base_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (moduleTotalMap G H f a), moduleTotalMap_over]
    rw [Category.assoc, Over.w f]
    exact G.base_eq.symm)

/-- A complement restriction uses the prescribed total-space map as a whole morphism. -/
structure ComplementMap {X Y : SmoothScheme k}
    {M : X.scheme.left.Modules} {N : Y.scheme.left.Modules} {d e : ℕ}
    (G : BundleGeometry X M d) (H : BundleGeometry Y N e)
    (f : X ⟶ Y) (a : M ⟶ (Scheme.Modules.pullback f.left).obj N) where
  map : G.complement ⟶ H.complement
  square : G.complementInclusion ≫ moduleSmoothMap G H f a = map ≫ H.complementInclusion

/-- The Thom map is the native pushout map of that exact complement square. -/
def thomMap {X Y : SmoothScheme k}
    {M : X.scheme.left.Modules} {N : Y.scheme.left.Modules} {d e : ℕ}
    (G : BundleGeometry X M d) (H : BundleGeometry Y N e)
    (f : X ⟶ Y) (a : M ⟶ (Scheme.Modules.pullback f.left).obj N)
    (C : ComplementMap G H f a) : G.thom ⟶ H.thom :=
  cofiberMap (representedMap G.complementInclusion) (representedMap H.complementInclusion)
    (representedMap C.map) (representedMap (moduleSmoothMap G H f a)) (by
      rw [← representedMap_comp, ← representedMap_comp, C.square])

end MathlibExt.AlgebraicGeometry.GeneralMotivicBundleFrameMaps
