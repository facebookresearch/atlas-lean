/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeMapGluingGeometry

/-!
# Actual maps to expanded P1 rubber targets

The original P1 is the actual O plus O subline projective bundle. Its
relative expansion at infinity is the recursively constructed standard
family; zero is the actual pulled original coordinate divisor. Positive
and negative signed markings impose full ideal contact at zero/infinity.
Nodes use the source's etale localized pure-contact condition.

Rubber arrows are actual scheme isomorphisms preserving both endpoint
ideals and the parameter, with every source marking/map square retained.
They include the original P1 scaling and all expanded-component scalings;
contraction to a chosen original P1 is not fixed by a rubber arrow.
Source: JPPZ arXiv:1602.04705v2, Section0.2.4, printed p6;
Jun Li arXiv:math/0009097v1 and math/0110113v1.
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

def zeroIdeal {T : Over (Spec (.of k))} (F : ExpandedFamily P R S T) :
    F.scheme.left.IdealSheafData :=
  (originalZero O P D).left.ker.comap F.contraction.left

abbrev Positive {n : ℕ} (a : Fin n → ℤ) := {i : Fin n // 0 < a i}
abbrev Negative {n : ℕ} (a : Fin n → ℤ) := {i : Fin n // a i < 0}

instance positiveFintype {n : ℕ} (a : Fin n → ℤ) : Fintype (Positive a) := Fintype.ofFinite _
instance negativeFintype {n : ℕ} (a : Fin n → ℤ) : Fintype (Negative a) := Fintype.ofFinite _

structure RubberFamily (T : Over (Spec (.of k))) (g n : ℕ) (a : Fin n → ℤ) where
  target : ExpandedFamily P R S T
  zeroCartier : CartierIdealModels.IsEffectiveCartier (zeroIdeal O P D R S target)
  curve : MarkedFamily T.left n g
  map : curve.X ⟶ target.scheme.left
  over : map ≫ target.projection.left = curve.π
  zeroContact : HasIndexedIdealContact map (zeroIdeal O P D R S target)
    (fun i : Positive a => curve.marking i.val) (fun i => (a i.val).natAbs)
  infinityContact : HasIndexedIdealContact map target.boundary.left.ker
    (fun i : Negative a => curve.marking i.val) (fun i => (a i.val).natAbs)
  predeformable : IsPredeformable curve.π target.projection.left map over

structure RubberTargetIso {T : Over (Spec (.of k))} (F H : ExpandedFamily P R S T) where
  iso : F.scheme ≅ H.scheme
  over : iso.hom ≫ H.projection = F.projection
  zero : (zeroIdeal O P D R S H).comap iso.hom.left = zeroIdeal O P D R S F
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
    {F H : ExpandedFamily P R S T} (f h : RubberTargetIso O P D R S F H)
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
  zero : ((zeroIdeal O P D R S F.target).comap
    (pullback.fst F.target.projection.left x)).comap target.hom =
    (zeroIdeal O P D R S F.target).comap (pullback.fst F.target.projection.left x)
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
