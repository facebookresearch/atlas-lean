/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeExpandedMapFamilies
public import MathlibExt.AlgebraicGeometry.GeneralStableMapCurveClasses

/-!
# Admissible relative-contact types and their actual family groupoids

Connected domain components, their genera and all ordered leg/root labels
are fixed by the type. A family has one common expanded target and actual
maps from those components. Arrows preserve every source marking and the
same target/map equations. Boundary evaluation acts on the actual global
root label, retaining disconnected admissible domains.
Source: Jun Li arXiv:math/0009097v1, Definitions4.6--4.8;
arXiv:math/0110113v1, Sections2.1/3.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeMapTypeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry RelativeProjectiveLineModels StandardRelativeExpansionModels
open ExpandedRelativeFamilies RelativeExpandedMapFamilies

/-- A relative (possibly disconnected) type with `n` legs and `r` roots on the relative divisor.
It has at least one vertex, so the glued types built from two of them (see
`RelativeMapGluingGeometry`) have both sides nonempty: Li's types with an empty side
(math/0009097v1, after (4.8)) are not covered here. -/
structure RelativeType (n r : ℕ) where
  vertices : ℕ
  nonempty : 0 < vertices
  legs : Fin vertices → ℕ
  roots : Fin vertices → ℕ
  genus : Fin vertices → ℕ
  legLabels : Fin n ≃ (Σ v : Fin vertices, Fin (legs v))
  rootLabels : Fin r ≃ (Σ v : Fin vertices, Fin (roots v))
  order : Fin r → ℕ
  positive : ∀ i, 0 < order i
  relativelyConnected : vertices = 1 ∨ ∀ v : Fin vertices, ∃ i : Fin r, (rootLabels i).1 = v

variable {k : Type} [Field k]
  (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (S : StandardSystem P R) {n r : ℕ} (G : RelativeType n r) (T : Over (Spec (.of k)))

structure TypeFamily where
  target : ExpandedFamily P R S T
  maps : ∀ v : Fin G.vertices,
    RelativeMapOn P R S T target (G.legs v) (G.roots v) (G.genus v)
      (fun i => G.order (G.rootLabels.symm ⟨v, i⟩))

def evaluation (F : TypeFamily P R S G T) (i : Fin r) : T ⟶ P.divisor :=
  rootEvaluation P R S T (F.maps (G.rootLabels i).1) (G.rootLabels i).2

def allEvaluations (F : TypeFamily P R S G T) : T ⟶ ∏ᶜ (fun _ : Fin r => P.divisor) :=
  Pi.lift (evaluation P R S G T F)

structure TypeIso (F H : TypeFamily P R S G T) where
  target : ExpandedIso P R S F.target H.target
  source : ∀ v : Fin G.vertices, (F.maps v).curve.X ≅ (H.maps v).curve.X
  over : ∀ v, (source v).hom ≫ (H.maps v).curve.π = (F.maps v).curve.π
  marking : ∀ (v : Fin G.vertices) (i : Fin (G.legs v + G.roots v)),
    (F.maps v).curve.marking i ≫ (source v).hom = (H.maps v).curve.marking i
  map : ∀ v, (source v).hom ≫ (H.maps v).map = (F.maps v).map ≫ target.iso.hom.left

@[ext] theorem TypeIso.ext {F H : TypeFamily P R S G T} (f h : TypeIso P R S G T F H)
    (target : f.target = h.target) (source : f.source = h.source) : f = h := by
  cases f
  cases h
  cases target
  cases source
  rfl

instance typeGroupoid : Groupoid (TypeFamily P R S G T) where
  Hom F H := TypeIso P R S G T F H
  id F :=
    { target := ⟨Iso.refl _, by simp, by simp, by simp⟩
      source := fun _ => Iso.refl _
      over := by intro v; simp
      marking := by intro v i; simp
      map := by intro v; simp }
  comp f h :=
    { target := ⟨f.target.iso ≪≫ h.target.iso, by simp [Category.assoc, h.target.over, f.target.over],
        by simp [Category.assoc, h.target.contraction, f.target.contraction],
        by simp [← Category.assoc, f.target.boundary, h.target.boundary]⟩
      source := fun v => f.source v ≪≫ h.source v
      over := by intro v; simp [Category.assoc, h.over, f.over]
      marking := by intro v i; simp [← Category.assoc, f.marking, h.marking]
      map := by
        intro v
        simp only [Iso.trans_hom, Over.comp_left]
        rw [Category.assoc, h.map, ← Category.assoc, f.map, Category.assoc] }
  inv f :=
    { target := ⟨f.target.iso.symm, by rw [← f.target.over]; simp,
        by rw [← f.target.contraction]; simp, by rw [← f.target.boundary]; simp⟩
      source := fun v => (f.source v).symm
      over := by intro v; rw [← f.over]; simp
      marking := by intro v i; rw [← f.marking]; simp
      map := by
        intro v
        dsimp only [Iso.symm_hom]
        apply (cancel_epi (f.source v).hom).1
        rw [← Category.assoc, (f.source v).hom_inv_id, Category.id_comp,
          ← Category.assoc, f.map, Category.assoc, ← Over.comp_left,
          f.target.iso.hom_inv_id, Over.id_left, Category.comp_id] }
  id_comp f := by apply TypeIso.ext <;> ext <;> simp
  comp_id f := by apply TypeIso.ext <;> ext <;> simp
  assoc f h j := by apply TypeIso.ext <;> ext <;> simp
  inv_comp f := by apply TypeIso.ext <;> ext <;> simp
  comp_inv f := by apply TypeIso.ext <;> ext <;> simp

def ofFixedType (F : TypeFamily P R S G T) : DisconnectedRelativeFamily P R S T n r G.order :=
  ⟨G.vertices, G.nonempty, G.legs, G.roots, G.genus, G.legLabels, G.rootLabels, F.target, F.maps⟩

def IsStableType (F : TypeFamily P R S G T) : Prop :=
  IsStableDisconnected P R S T (ofFixedType P R S G T F)

variable [LocallyOfFiniteType P.target.hom] [IsNoetherian P.target.left]

/-- The degree is the actual pushed curve class after contraction to the
original target, with its native all-field class/base-change normalization.

This is a Chow-refined type: it fixes the rational Chow class of each vertex's pushed curve on
every geometric fibre, which refines Li's fixed degree with respect to a polarisation
(math/0009097v1, Defs. 4.6–4.7). The stable families of this type form the corresponding
subfunctor of Li's moduli; in a family of Li's fixed degree the Chow classes may vary (for
`E × ℙ¹` relative to `E × {∞}`, the fibres `{p} × ℙ¹` have fixed degree and contact but classes
differing by `p − q`), so the two agree only when such classes are locally constant. -/
def HasVertexClasses
    (beta : Fin G.vertices → RelativeCurveClasses.CurveClass P.target)
    (F : TypeFamily P R S G T) : Prop :=
  ∀ v : Fin G.vertices, GeneralStableMapFamilies.HasCurveClass P.target T
    (contractedFamily P R S T (F.maps v)) (beta v)

abbrev StableTypeFamily
    (beta : Fin G.vertices → RelativeCurveClasses.CurveClass P.target) :=
  (show ObjectProperty (TypeFamily P R S G T) from
    fun F => IsStableType P R S G T F ∧ HasVertexClasses P R S G T beta F).FullSubcategory

end MathlibExt.AlgebraicGeometry.RelativeMapTypeModels
