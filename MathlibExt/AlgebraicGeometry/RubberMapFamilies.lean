/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeMapGluingGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Actual maps to expanded P1 rubber targets

The original P1 is the actual O plus O subline projective bundle. Its
relative expansion at infinity is the recursively constructed standard
family; zero is the actual pulled original coordinate divisor. Positive
and negative signed markings impose full ideal contact at zero/infinity.
Nodes use the source's etale localized pure-contact condition.

A framed expanded target (`ExpandedFamily`) has a contraction to the fixed original P1,
which on the unexpanded locus trivialises the target together with both of its ends. A rubber
target (`RubberTarget`) keeps only its projection, its zero ideal and its boundary, and is framed
fppf-locally on the base. In a family it may be a twisted form of a framed target, such as the
projective completion of a line bundle `L` on the base with its zero and infinity sections
(Marcus–Wise, Sections 2.1–2.2), which has no global frame when `L` is nontrivial. Rubber
families of maps have such targets, so they are closed under descent.

Rubber arrows are actual scheme isomorphisms preserving both endpoint
ideals and the parameter, with every source marking/map square retained.
They include the original P1 scaling and all expanded-component scalings;
contraction to a chosen original P1 is not fixed by a rubber arrow.
Source: JPPZ arXiv:1602.04705v2, Section0.2.4, printed p6;
Jun Li arXiv:math/0009097v1 and math/0110113v1;
Marcus–Wise arXiv:1310.5981, Sections 2.1–2.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RubberMapFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open RelativeProjectiveLineModels ExpandedTargetChainGeometry StandardRelativeExpansionModels
open ExpandedRelativeFamilies RelativeContactGeometry RelativeExpandedMapFamilies
open MarkedCurveStabilization CoherentCurveLinearSeries

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k))

structure OriginalRubberPair where
  target : P.target ≅ Over.mk O.projection
  divisor : P.divisor ≅ Over.mk (𝟙 (Spec (.of k)))
  infinity : P.inclusion ≫ target.hom = divisor.hom ≫
    (Over.homMk O.infinity O.infinity_over : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk O.projection)

variable (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)

def originalZero : Over.mk (𝟙 (Spec (.of k))) ⟶ P.target :=
  (Over.homMk O.zero O.zero_over : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk O.projection) ≫ D.target.inv

/-- The zero ideal of a framed expanded target: the original zero point pulled back along the
contraction to the original target. -/
def zeroIdeal {T : Over (Spec (.of k))} (F : ExpandedFamily P R S T) :
    F.scheme.left.IdealSheafData :=
  (originalZero O P D).left.ker.comap F.contraction.left

/-- A frame at a point `t` of the base of a family `p : X ⟶ T` with a zero ideal and a
boundary: over an fppf neighbourhood of `t`, an isomorphism of the pulled-back family with a
framed expanded target, preserving the projection and both ends. -/
structure RubberFrame {T X : Over (Spec (.of k))} (p : X ⟶ T) (zero : X.left.IdealSheafData)
    (boundary : prod P.divisor T ⟶ X) (t : T.left) where
  /-- The fppf neighbourhood of `t`. -/
  neighborhood : Over (Spec (.of k))
  /-- Its map to the base. -/
  map : neighborhood ⟶ T
  [flat : Flat map.left]
  [finitePresentation : LocallyOfFinitePresentation map.left]
  contains : t ∈ Set.range map.left
  /-- The framed expanded target over the neighbourhood. -/
  family : ExpandedFamily P R S neighborhood
  /-- The identification of the pulled-back family with it. -/
  comparison : pullback p map ≅ family.scheme
  projection : comparison.hom ≫ family.projection = pullback.snd p map
  zero_eq : (zeroIdeal O P D R S family).comap comparison.hom.left =
    zero.comap (pullback.fst p map).left
  infinity_eq : family.boundary.left.ker.comap comparison.hom.left =
    boundary.left.ker.comap (pullback.fst p map).left

/-- A rubber target over `T`: a family over `T` with its zero ideal and its boundary (the end
at infinity) which is framed fppf-locally on `T`. There is no global contraction to the original
target: a twisted form of a framed target, such as the projective completion of a nontrivial line
bundle on `T` with its zero and infinity sections, is a rubber target. -/
structure RubberTarget (T : Over (Spec (.of k))) where
  /-- The total family. -/
  scheme : Over (Spec (.of k))
  /-- Its projection to the base. -/
  projection : scheme ⟶ T
  /-- The ideal of the end at zero. -/
  zero : scheme.left.IdealSheafData
  /-- The end at infinity. -/
  boundary : prod P.divisor T ⟶ scheme
  [closed : IsClosedImmersion boundary.left]
  cartier : CartierIdealModels.IsEffectiveCartier boundary.left.ker
  boundary_projection : boundary ≫ projection = prod.snd
  framed : ∀ t : T.left, Nonempty (RubberFrame O P D R S projection zero boundary t)

attribute [instance] RubberTarget.closed

/-- A framed expanded target is a rubber target, framed over the identity of its base, with
the zero ideal of its contraction. -/
def RubberTarget.ofFramed {T : Over (Spec (.of k))} (F : ExpandedFamily P R S T) :
    RubberTarget O P D R S T where
  scheme := F.scheme
  projection := F.projection
  zero := zeroIdeal O P D R S F
  boundary := F.boundary
  cartier := F.cartier
  boundary_projection := F.boundary_projection
  framed t := ⟨{
    neighborhood := T
    map := 𝟙 T
    contains := ⟨t, by simp⟩
    family := F
    comparison := asIso (pullback.fst F.projection (𝟙 T))
    projection := by simpa using pullback.condition (f := F.projection) (g := 𝟙 T)
    zero_eq := rfl
    infinity_eq := rfl }⟩

/-- A family framed over the members of an fppf covering of its base is a rubber target. The
frames need not glue to a global frame. -/
def RubberTarget.ofCover {T X : Over (Spec (.of k))} (p : X ⟶ T) (zero : X.left.IdealSheafData)
    (boundary : prod P.divisor T ⟶ X) [IsClosedImmersion boundary.left]
    (cartier : CartierIdealModels.IsEffectiveCartier boundary.left.ker)
    (boundary_projection : boundary ≫ p = prod.snd) {ι : Type} (U : ι → Over (Spec (.of k)))
    (q : ∀ i, U i ⟶ T) [∀ i, Flat (q i).left] [∀ i, LocallyOfFinitePresentation (q i).left]
    (cover : ∀ t : T.left, ∃ i, t ∈ Set.range (q i).left)
    (F : ∀ i, ExpandedFamily P R S (U i)) (e : ∀ i, pullback p (q i) ≅ (F i).scheme)
    (projection : ∀ i, (e i).hom ≫ (F i).projection = pullback.snd p (q i))
    (zero_eq : ∀ i, (zeroIdeal O P D R S (F i)).comap (e i).hom.left =
      zero.comap (pullback.fst p (q i)).left)
    (infinity_eq : ∀ i, (F i).boundary.left.ker.comap (e i).hom.left =
      boundary.left.ker.comap (pullback.fst p (q i)).left) :
    RubberTarget O P D R S T where
  scheme := X
  projection := p
  zero := zero
  boundary := boundary
  cartier := cartier
  boundary_projection := boundary_projection
  framed t := (cover t).elim fun i hi => ⟨{
    neighborhood := U i
    map := q i
    contains := hi
    family := F i
    comparison := e i
    projection := projection i
    zero_eq := zero_eq i
    infinity_eq := infinity_eq i }⟩

variable {O P D R S} in
/-- An identification of a rubber target with the pullback of the standard length-`m` target
along a parameter map, preserving the projection, the zero ideal and the boundary. It frames the
target by the contraction of the standard target. -/
structure RubberTarget.StandardFrame {T : Over (Spec (.of k))} (X : RubberTarget O P D R S T)
    (m : ℕ) (f : T ⟶ ExpansionParameterModels.ParameterSpace k m) where
  comparison : X.scheme ≅ pullback (S.chart m).projection f
  projection : comparison.hom ≫ pullback.snd (S.chart m).projection f = X.projection
  zero : ((originalZero O P D).left.ker.comap
    (pullback.fst (S.chart m).projection f ≫ (S.chart m).contraction ≫ prod.fst).left).comap
      comparison.hom.left = X.zero
  boundary : X.boundary ≫ comparison.hom = standardBoundaryLift P R S T f

abbrev Positive {n : ℕ} (a : Fin n → ℤ) := {i : Fin n // 0 < a i}
abbrev Negative {n : ℕ} (a : Fin n → ℤ) := {i : Fin n // a i < 0}

instance positiveFintype {n : ℕ} (a : Fin n → ℤ) : Fintype (Positive a) := Fintype.ofFinite _
instance negativeFintype {n : ℕ} (a : Fin n → ℤ) : Fintype (Negative a) := Fintype.ofFinite _

/-- A family of maps to rubber over `T`: a marked curve with a map to a rubber target, with
signed full contact at the two ends. -/
structure RubberFamily (T : Over (Spec (.of k))) (g n : ℕ) (a : Fin n → ℤ) where
  target : RubberTarget O P D R S T
  zeroCartier : CartierIdealModels.IsEffectiveCartier target.zero
  curve : MarkedFamily T.left n g
  map : curve.X ⟶ target.scheme.left
  over : map ≫ target.projection.left = curve.π
  zeroContact : HasIndexedIdealContact map target.zero
    (fun i : Positive a => curve.marking i.val) (fun i => (a i.val).natAbs)
  infinityContact : HasIndexedIdealContact map target.boundary.left.ker
    (fun i : Negative a => curve.marking i.val) (fun i => (a i.val).natAbs)
  predeformable : IsPredeformable curve.π target.projection.left map over

structure RubberTargetIso {T : Over (Spec (.of k))} (F H : RubberTarget O P D R S T) where
  iso : F.scheme ≅ H.scheme
  over : iso.hom ≫ H.projection = F.projection
  zero : H.zero.comap iso.hom.left = F.zero
  infinity : H.boundary.left.ker.comap iso.hom.left = F.boundary.left.ker

structure RubberIso {T : Over (Spec (.of k))} {g n : ℕ} {a : Fin n → ℤ}
    (F H : RubberFamily O P D R S T g n a) where
  source : F.curve.X ≅ H.curve.X
  target : RubberTargetIso O P D R S F.target H.target
  over : source.hom ≫ H.curve.π = F.curve.π
  markings : ∀ i : Fin n, F.curve.marking i ≫ source.hom = H.curve.marking i
  map : source.hom ≫ H.map = F.map ≫ target.iso.hom.left

@[ext] theorem RubberIso.ext {T : Over (Spec (.of k))} {g n : ℕ} {a : Fin n → ℤ}
    {F H : RubberFamily O P D R S T g n a} (f h : RubberIso O P D R S F H)
    (source : f.source = h.source) (target : f.target = h.target) : f = h := by
  cases f
  cases h
  cases source
  cases target
  rfl

@[ext] theorem RubberTargetIso.ext {T : Over (Spec (.of k))}
    {F H : RubberTarget O P D R S T} (f h : RubberTargetIso O P D R S F H)
    (iso : f.iso = h.iso) : f = h := by
  cases f
  cases h
  cases iso
  rfl

instance rubberGroupoid (T : Over (Spec (.of k))) (g n : ℕ) (a : Fin n → ℤ) :
    Groupoid (RubberFamily O P D R S T g n a) where
  Hom F H := RubberIso O P D R S F H
  id F :=
    { source := Iso.refl _
      target := ⟨Iso.refl _, by simp, by simp, by simp⟩
      over := by simp
      markings := by intro i; simp
      map := by simp }
  comp f h :=
    { source := f.source ≪≫ h.source
      target :=
        ⟨f.target.iso ≪≫ h.target.iso,
          by simp [Category.assoc, h.target.over, f.target.over],
          by simp only [Iso.trans_hom, Over.comp_left, Scheme.IdealSheafData.comap_comp,
            h.target.zero, f.target.zero],
          by simp only [Iso.trans_hom, Over.comp_left, Scheme.IdealSheafData.comap_comp,
            h.target.infinity, f.target.infinity]⟩
      over := by simp [Category.assoc, h.over, f.over]
      markings := by intro i; simp [← Category.assoc, f.markings, h.markings]
      map := by
        simp only [Iso.trans_hom, Over.comp_left]
        rw [Category.assoc, h.map, ← Category.assoc, f.map, Category.assoc] }
  inv f :=
    { source := f.source.symm
      target :=
        ⟨f.target.iso.symm, by rw [← f.target.over]; simp,
          by
            dsimp only [Iso.symm_hom]
            rw [← f.target.zero, ← Scheme.IdealSheafData.comap_comp, ← Over.comp_left,
              f.target.iso.inv_hom_id, Over.id_left, Scheme.IdealSheafData.comap_id],
          by
            dsimp only [Iso.symm_hom]
            rw [← f.target.infinity, ← Scheme.IdealSheafData.comap_comp, ← Over.comp_left,
              f.target.iso.inv_hom_id, Over.id_left, Scheme.IdealSheafData.comap_id]⟩
      over := by rw [← f.over]; simp
      markings := by intro i; rw [← f.markings]; simp
      map := by
        dsimp only [Iso.symm_hom]
        apply (cancel_epi f.source.hom).1
        rw [← Category.assoc, f.source.hom_inv_id, Category.id_comp,
          ← Category.assoc, f.map, Category.assoc, ← Over.comp_left,
          f.target.iso.hom_inv_id, Over.id_left, Category.comp_id] }
  id_comp f := by apply RubberIso.ext <;> ext <;> simp
  comp_id f := by apply RubberIso.ext <;> ext <;> simp
  assoc f h j := by apply RubberIso.ext <;> ext <;> simp
  inv_comp f := by apply RubberIso.ext <;> ext <;> simp
  comp_inv f := by apply RubberIso.ext <;> ext <;> simp

def fibreMap {T : Over (Spec (.of k))} {g n : ℕ} {a : Fin n → ℤ}
    (F : RubberFamily O P D R S T g n a) {Ω : Type} [Field Ω] (x : Spec (.of Ω) ⟶ T.left) :
    pullback F.curve.π x ⟶ pullback F.target.projection.left x :=
  pullback.lift (pullback.fst F.curve.π x ≫ F.map) (pullback.snd F.curve.π x) (by
    rw [Category.assoc, F.over]
    exact pullback.condition)

structure GeometricAutomorphism {T : Over (Spec (.of k))} {g n : ℕ} {a : Fin n → ℤ}
    (F : RubberFamily O P D R S T g n a) (Ω : Type) [Field Ω] (x : Spec (.of Ω) ⟶ T.left) where
  source : pullback F.curve.π x ≅ pullback F.curve.π x
  target : pullback F.target.projection.left x ≅ pullback F.target.projection.left x
  source_over : source.hom ≫ pullback.snd F.curve.π x = pullback.snd F.curve.π x
  target_over : target.hom ≫ pullback.snd F.target.projection.left x =
    pullback.snd F.target.projection.left x
  zero : (F.target.zero.comap
    (pullback.fst F.target.projection.left x)).comap target.hom =
    F.target.zero.comap (pullback.fst F.target.projection.left x)
  infinity : (F.target.boundary.left.ker.comap
    (pullback.fst F.target.projection.left x)).comap target.hom =
    F.target.boundary.left.ker.comap (pullback.fst F.target.projection.left x)
  markings : ∀ i : Fin n,
    fiberMark F.curve.π (F.curve.marking i) (F.curve.section_eq i) x ≫ source.hom =
      fiberMark F.curve.π (F.curve.marking i) (F.curve.section_eq i) x
  map : source.hom ≫ fibreMap O P D R S F x = fibreMap O P D R S F x ≫ target.hom

def IsStableRubber {T : Over (Spec (.of k))} {g n : ℕ} {a : Fin n → ℤ}
    (F : RubberFamily O P D R S T g n a) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T.left),
    Finite (GeometricAutomorphism O P D R S F Ω x)

end MathlibExt.AlgebraicGeometry.RubberMapFamilies
