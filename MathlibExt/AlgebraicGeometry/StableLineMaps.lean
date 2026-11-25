/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.MarkedCurveStabilization
public import MathlibExt.AlgebraicGeometry.AlgebraicBundleGeometry
public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
/-!
# Actual degree-one stable-map families and their quotient flags

The source curve is an actual flat proper genus-zero nodal scheme family,
with one smooth marking. Degree and finite map-preserving automorphisms are
checked after every algebraically closed field base change. The degree-one
map goes to the given universal projective-space quotient, not an abstract
stable-object carrier.

The family and quotient-flag groupoids and their inverses are constructed
here. The flag attached to a map is fixed by the actual module sheaves
`π_* f* O(1)` and `s* f* O(1)`, with coordinate and marking arrows computed
using Mathlib's pullback/pushforward adjunction. The Euler cokernel and its
actual derived direct image are the relative map-deformation model. No
existence of the moduli equivalence or vanishing theorem is asserted here.

Reference: Fulton--Pandharipande, *Notes on stable maps and quantum
cohomology*, https://arxiv.org/abs/alg-geom/9608011, §§1--3. The marked-curve
and positive-rank projective-bundle primitives are reused from the completed
local support and the cited public Axiom/TauCeti constructions; those
primitive constructions are not new requests in this packet.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.StableLineMaps
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification MarkedCurveStabilization CoherentCurveLinearSeries
open AlgebraicBundleGeometry
attribute [local instance] HasDerivedCategory.standard

abbrev Point : ComplexScheme := Over.mk (𝟙 (Spec (.of ℂ)))
abbrev targetGenerators (r : ℕ) : Point.left.Modules :=
  SheafOfModules.free (R := Point.left.ringCatSheaf) (Fin (r + 1))

variable (r : ℕ) (X : ProjectiveBundle Point 0 r (targetGenerators r))

def mapAut {T : Scheme.{0}} (C : MarkedFamily T 1 0) (f : C.X ⟶ X.total.left)
    {Ω : Type} [Field Ω] (p : Spec (.of Ω) ⟶ T) :=
  {e : fiberCurve C.π p ≅ fiberCurve C.π p //
    e.hom.left ≫ pullback.fst C.π p ≫ f = pullback.fst C.π p ≫ f ∧
      fiberMark C.π (C.marking 0) (C.section_eq 0) p ≫ e.hom.left =
        fiberMark C.π (C.marking 0) (C.section_eq 0) p}

structure StableLineFamily (T : ComplexScheme) where
  curve : MarkedFamily T.left 1 0
  map : curve.X ⟶ X.total.left
  over : map ≫ X.projection.left = curve.π ≫ T.hom
  degree : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T.left),
    ∃ (_ : IsProperCurve (fiberCurve curve.π p).hom)
      (hL : IsLineBundle
        ((Scheme.Modules.pullback (pullback.fst curve.π p ≫ map)).obj X.tautological)),
      CoherentCurveLinearSeries.degree (fiberCurve curve.π p).hom
        ((Scheme.Modules.pullback (pullback.fst curve.π p ≫ map)).obj X.tautological) hL = 1
  stable : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ T.left),
    Finite (mapAut r X curve map p)

variable {r X} {T : ComplexScheme} (F : StableLineFamily r X T)

abbrev curveLine := (Scheme.Modules.pullback F.map).obj X.tautological
abbrev curveOver : ComplexScheme := Over.mk (F.curve.π ≫ T.hom)
def curveProjection : curveOver F ⟶ T := Over.homMk F.curve.π rfl

def evaluation : T ⟶ X.total :=
  Over.homMk (F.curve.marking 0 ≫ F.map) (by
    have hp : X.projection.left = X.total.hom := by simpa using X.projection.w
    rw [← hp, Category.assoc, F.over, ← Category.assoc, F.curve.section_eq 0, Category.id_comp])

def targetCoordinate (i : Fin (r + 1)) : structureModule X.total.left ⟶ X.tautological :=
  (pullbackUnit X.total.left Point.left X.projection.left).inv ≫
    (Scheme.Modules.pullback X.projection.left).map (SheafOfModules.ιFree i) ≫ X.quotient

abbrev targetEulerBundle : X.total.left.Modules := ∏ᶜ fun _ : Fin (r + 1) => X.tautological

def targetEulerMap : structureModule X.total.left ⟶ targetEulerBundle (r := r) (X := X) :=
  Pi.lift (fun i => targetCoordinate (r := r) (X := X) i)

abbrev targetTangent : X.total.left.Modules := cokernel (targetEulerMap (r := r) (X := X))
abbrev mapTangent := (Scheme.Modules.pullback F.map).obj (targetTangent (r := r) (X := X))

abbrev tangentComplex : DerivedCategory T.left.Modules :=
  DerivedCategory.Plus.ι.obj
    (((Scheme.Modules.pushforward F.curve.π).rightDerivedFunctorPlus).obj
      ((DerivedCategory.Plus.singleFunctor F.curve.X.Modules 0).obj (mapTangent F)))

abbrev deformationModule (i : ℕ) (J : T.left.Modules) : T.left.Modules :=
  ((Scheme.Modules.pushforward F.curve.π).rightDerived i).obj
    (AlgebraicLineBundleFamilies.moduleTensor F.curve.X (mapTangent F)
      ((Scheme.Modules.pullback F.curve.π).obj J))

abbrev quotientModule : T.left.Modules := (Scheme.Modules.pushforward F.curve.π).obj (curveLine F)
abbrev markedLine : T.left.Modules :=
  (Scheme.Modules.pullback (F.curve.marking 0)).obj (curveLine F)
abbrev baseGenerators : T.left.Modules := (Scheme.Modules.pullback T.hom).obj (targetGenerators r)

def coordinateQuotient : baseGenerators (r := r) (T := T) ⟶ quotientModule F :=
  (Scheme.Modules.pullbackPushforwardAdjunction F.curve.π).homEquiv _ _
    ((Scheme.Modules.pullbackComp F.curve.π T.hom).hom.app (targetGenerators r) ≫
      (Scheme.Modules.pullbackCongr F.over.symm).hom.app (targetGenerators r) ≫
      (Scheme.Modules.pullbackComp F.map X.projection.left).inv.app (targetGenerators r) ≫
      (Scheme.Modules.pullback F.map).map X.quotient)

def markingQuotient : quotientModule F ⟶ markedLine F :=
  (Scheme.Modules.pullbackId T.left).inv.app (quotientModule F) ≫
    (Scheme.Modules.pullbackCongr (F.curve.section_eq 0).symm).hom.app (quotientModule F) ≫
    (Scheme.Modules.pullbackComp (F.curve.marking 0) F.curve.π).inv.app (quotientModule F) ≫
    (Scheme.Modules.pullback (F.curve.marking 0)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction F.curve.π).counit.app (curveLine F))

structure FamilyHom (G : StableLineFamily r X T) where
  iso : F.curve.X ≅ G.curve.X
  over : iso.hom ≫ G.curve.π = F.curve.π
  marking : F.curve.marking 0 ≫ iso.hom = G.curve.marking 0
  map : iso.hom ≫ G.map = F.map

@[ext] theorem familyHom_ext {G : StableLineFamily r X T} {a b : FamilyHom F G}
    (h : a.iso = b.iso) : a = b := by cases a; cases b; cases h; rfl

instance familyGroupoid : Groupoid (StableLineFamily r X T) where
  Hom F G := FamilyHom F G
  id F := ⟨Iso.refl _, by simp, by simp, by simp⟩
  comp a b := ⟨a.iso ≪≫ b.iso, by simp [Category.assoc, b.over, a.over],
    by simp [← Category.assoc, a.marking, b.marking], by simp [Category.assoc, b.map, a.map]⟩
  inv a := ⟨a.iso.symm, by rw [← a.over]; simp,
    by rw [← a.marking]; simp, by rw [← a.map]; simp⟩
  id_comp a := by apply familyHom_ext; ext; simp
  comp_id a := by apply familyHom_ext; ext; simp
  assoc a b c := by apply familyHom_ext; ext; simp
  inv_comp a := by apply familyHom_ext; ext; simp

variable (r X T)

structure QuotientFlag where
  quotient : T.left.Modules
  line : T.left.Modules
  rankTwo : IsBundle quotient 2
  rankOne : IsLine line
  first : baseGenerators (r := r) (T := T) ⟶ quotient
  second : quotient ⟶ line
  [firstEpi : Epi first]
  [secondEpi : Epi second]
attribute [instance] QuotientFlag.firstEpi QuotientFlag.secondEpi

variable {r X T}

structure FlagHom (A B : QuotientFlag r T) where
  quotient : A.quotient ≅ B.quotient
  line : A.line ≅ B.line
  first : A.first ≫ quotient.hom = B.first
  second : quotient.hom ≫ B.second = A.second ≫ line.hom

@[ext] theorem flagHom_ext {A B : QuotientFlag r T} {a b : FlagHom A B}
    (hq : a.quotient = b.quotient) (hl : a.line = b.line) : a = b := by
  cases a; cases b; cases hq; cases hl; rfl

instance flagGroupoid : Groupoid (QuotientFlag r T) where
  Hom A B := FlagHom A B
  id A := ⟨Iso.refl _, Iso.refl _, by simp, by simp⟩
  comp a b := ⟨a.quotient ≪≫ b.quotient, a.line ≪≫ b.line,
    by simp [← Category.assoc, a.first, b.first],
    by simp [Category.assoc, b.second, ← a.second]⟩
  inv a := ⟨a.quotient.symm, a.line.symm,
    by rw [← a.first]; simp,
    by simpa [Category.assoc] using
      congrArg (fun f => a.quotient.inv ≫ f ≫ a.line.inv) a.second.symm⟩
  id_comp a := by apply flagHom_ext <;> ext <;> simp
  comp_id a := by apply flagHom_ext <;> ext <;> simp
  assoc a b c := by apply flagHom_ext <;> ext <;> simp
  inv_comp a := by apply flagHom_ext <;> ext <;> simp

structure StableLineModuliComparison (r : ℕ)
    (X : ProjectiveBundle Point 0 r (targetGenerators r)) (T : ComplexScheme) where
  equivalence : StableLineFamily r X T ≌ QuotientFlag r T
  quotientIso : ∀ F : StableLineFamily r X T,
    (equivalence.functor.obj F).quotient ≅ quotientModule F
  lineIso : ∀ F : StableLineFamily r X T, (equivalence.functor.obj F).line ≅ markedLine F
  coordinate : ∀ F : StableLineFamily r X T,
    (equivalence.functor.obj F).first ≫ (quotientIso F).hom = coordinateQuotient F
  marking : ∀ F : StableLineFamily r X T,
    (quotientIso F).inv ≫ (equivalence.functor.obj F).second ≫ (lineIso F).hom = markingQuotient F

structure FamilyBaseChange {T' : ComplexScheme} (h : T' ⟶ T)
    (F' : StableLineFamily r X T') where
  curveMap : F'.curve.X ⟶ F.curve.X
  square : IsPullback curveMap F'.curve.π F.curve.π h.left
  map : curveMap ≫ F.map = F'.map
  marking : F'.curve.marking 0 ≫ curveMap = h.left ≫ F.curve.marking 0

def quotientBaseChange {T' : ComplexScheme} {h : T' ⟶ T}
    {F' : StableLineFamily r X T'} (b : FamilyBaseChange F h F') :
    (Scheme.Modules.pullback h.left).obj (quotientModule F) ⟶ quotientModule F' :=
  (Scheme.Modules.pullbackPushforwardAdjunction F'.curve.π).homEquiv _ _
    ((Scheme.Modules.pullbackComp F'.curve.π h.left).hom.app (quotientModule F) ≫
      (Scheme.Modules.pullbackCongr b.square.w.symm).hom.app (quotientModule F) ≫
      (Scheme.Modules.pullbackComp b.curveMap F.curve.π).inv.app (quotientModule F) ≫
      (Scheme.Modules.pullback b.curveMap).map
        ((Scheme.Modules.pullbackPushforwardAdjunction F.curve.π).counit.app (curveLine F)) ≫
      (Scheme.Modules.pullbackComp b.curveMap F.map).hom.app X.tautological ≫
      (Scheme.Modules.pullbackCongr b.map).hom.app X.tautological)


end MathlibExt.AlgebraicGeometry.StableLineMaps
