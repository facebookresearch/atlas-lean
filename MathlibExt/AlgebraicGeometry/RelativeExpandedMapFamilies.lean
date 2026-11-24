/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeContactGeometry
public import MathlibExt.AlgebraicGeometry.GeneralStableMapFamilies

/-!
# Actual marked maps to expanded relative families

The source is an actual marked nodal curve and the target is an actual
expanded family. Root markings factor through its distinguished divisor,
and their full pulled-ideal powers impose contact. Predeformability uses
the actual etale node lifts and localized pure-contact equations. Boundary
evaluation is the literal root lift followed by the divisor projection.

The groupoid retains actual source/target isomorphisms, all markings and
the map square. Geometric stability tests the combined automorphisms of
the actual source and expanded target fibre, fixing the original target.
Source: Jun Li arXiv:math/0009097v1, Definition4.7/Section4.3;
arXiv:math/0110113v1, Definitions1.2/1.4 and Section2.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeExpandedMapFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry ExpansionParameterModels StandardRelativeExpansionModels
open ExpandedRelativeFamilies RelativeProjectiveLineModels RelativeContactGeometry
open MarkedCurveStabilization

variable {k : Type} [Field k]
  (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (S : StandardSystem P R) (T : Over (Spec (.of k)))

def IsRelativeNode {X T : Scheme.{0}} (p : X ⟶ T) (x : X) : Prop :=
  ¬ ∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ p)

def IsPredeformable {C X T : Scheme.{0}} (p : C ⟶ T) (q : X ⟶ T) (f : C ⟶ X)
    (comm : f ≫ q = p) : Prop :=
  ∀ x : C, IsRelativeNode q (f x) →
    ∃ N : EtaleNodePresentation p q f comm x, ∃ m : ℕ, Nonempty (PureContact N.chart m)

structure RelativeMapOn (F : ExpandedFamily P R S T) (n r g : ℕ) (order : Fin r → ℕ) where
  curve : MarkedFamily T.left (n + r) g
  map : curve.X ⟶ F.scheme.left
  over : map ≫ F.projection.left = curve.π
  contact : HasBoundaryContact map F.boundary.left
    (fun i : Fin r => curve.marking (Fin.natAdd n i)) order
  rootLift : Fin r → (T ⟶ prod P.divisor T)
  root_projection : ∀ i, rootLift i ≫ prod.snd = 𝟙 T
  root_map : ∀ i,
    (rootLift i).left ≫ F.boundary.left = curve.marking (Fin.natAdd n i) ≫ map
  predeformable : IsPredeformable curve.π F.projection.left map over

def rootEvaluation {F : ExpandedFamily P R S T} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S T F n r g order) (i : Fin r) : T ⟶ P.divisor :=
  f.rootLift i ≫ prod.fst

def simultaneousEvaluation {F : ExpandedFamily P R S T} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S T F n r g order) : T ⟶ ∏ᶜ (fun _ : Fin r => P.divisor) :=
  Pi.lift (rootEvaluation P R S T f)

structure RelativeFamily (n r g : ℕ) (order : Fin r → ℕ) where
  target : ExpandedFamily P R S T
  map : RelativeMapOn P R S T target n r g order

structure RelativeIso {n r g : ℕ} {order : Fin r → ℕ}
    (F G : RelativeFamily P R S T n r g order) where
  source : F.map.curve.X ≅ G.map.curve.X
  target : ExpandedIso P R S F.target G.target
  over : source.hom ≫ G.map.curve.π = F.map.curve.π
  marking : ∀ i : Fin (n + r), F.map.curve.marking i ≫ source.hom = G.map.curve.marking i
  map : source.hom ≫ G.map.map = F.map.map ≫ target.iso.hom.left

@[ext] theorem RelativeIso.ext {n r g : ℕ} {order : Fin r → ℕ}
    {F G : RelativeFamily P R S T n r g order} (f h : RelativeIso P R S T F G)
    (source : f.source = h.source) (target : f.target = h.target) : f = h := by
  cases f
  cases h
  cases source
  cases target
  rfl

instance relativeGroupoid (n r g : ℕ) (order : Fin r → ℕ) :
    Groupoid (RelativeFamily P R S T n r g order) where
  Hom F G := RelativeIso P R S T F G
  id F := ⟨Iso.refl _, ⟨Iso.refl _, by simp, by simp, by simp⟩,
    by simp, by intro i; simp, by simp⟩
  comp f h := ⟨f.source ≪≫ h.source,
    ⟨f.target.iso ≪≫ h.target.iso, by simp [Category.assoc, h.target.over, f.target.over],
      by simp [Category.assoc, h.target.contraction, f.target.contraction],
      by simp [← Category.assoc, f.target.boundary, h.target.boundary]⟩,
    by simp [Category.assoc, h.over, f.over],
    by intro i; simp [← Category.assoc, f.marking, h.marking],
    by
      simp only [Iso.trans_hom, Over.comp_left]
      rw [Category.assoc, h.map, ← Category.assoc, f.map, Category.assoc]⟩
  inv f := ⟨f.source.symm,
    ⟨f.target.iso.symm, by rw [← f.target.over]; simp,
      by rw [← f.target.contraction]; simp, by rw [← f.target.boundary]; simp⟩,
    by rw [← f.over]; simp, by intro i; rw [← f.marking i]; simp,
    by
      dsimp only [Iso.symm_hom]
      apply (cancel_epi f.source.hom).1
      rw [← Category.assoc, f.source.hom_inv_id, Category.id_comp,
        ← Category.assoc, f.map, Category.assoc, ← Over.comp_left,
        f.target.iso.hom_inv_id, Over.id_left, Category.comp_id]⟩
  id_comp f := by apply RelativeIso.ext <;> ext <;> simp
  comp_id f := by apply RelativeIso.ext <;> ext <;> simp
  assoc f h j := by apply RelativeIso.ext <;> ext <;> simp
  inv_comp f := by apply RelativeIso.ext <;> ext <;> simp
  comp_inv f := by apply RelativeIso.ext <;> ext <;> simp

def fibreMap {F : ExpandedFamily P R S T} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S T F n r g order) {Ω : Type} [Field Ω] (x : Spec (.of Ω) ⟶ T.left) :
    pullback f.curve.π x ⟶ pullback F.projection.left x :=
  pullback.lift (pullback.fst f.curve.π x ≫ f.map) (pullback.snd f.curve.π x) (by
    rw [Category.assoc, f.over]
    exact pullback.condition)

structure GeometricAutomorphism {F : ExpandedFamily P R S T} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S T F n r g order) (Ω : Type) [Field Ω] (x : Spec (.of Ω) ⟶ T.left) where
  source : pullback f.curve.π x ≅ pullback f.curve.π x
  target : pullback F.projection.left x ≅ pullback F.projection.left x
  source_over : source.hom ≫ pullback.snd f.curve.π x = pullback.snd f.curve.π x
  target_over : target.hom ≫ pullback.snd F.projection.left x = pullback.snd F.projection.left x
  contraction : target.hom ≫ pullback.fst F.projection.left x ≫ F.contraction.left =
    pullback.fst F.projection.left x ≫ F.contraction.left
  boundary : (F.boundary.left.ker.comap (pullback.fst F.projection.left x)).comap target.hom =
    F.boundary.left.ker.comap (pullback.fst F.projection.left x)
  marking : ∀ i : Fin (n + r),
    fiberMark f.curve.π (f.curve.marking i) (f.curve.section_eq i) x ≫ source.hom =
      fiberMark f.curve.π (f.curve.marking i) (f.curve.section_eq i) x
  map : source.hom ≫ fibreMap P R S T f x = fibreMap P R S T f x ≫ target.hom

def IsStableRelative {F : ExpandedFamily P R S T} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S T F n r g order) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T.left),
    Finite (GeometricAutomorphism P R S T f Ω x)

/-- A disconnected admissible domain has finite actual labelled components,
with exact global leg/root bijections and one common expanded target. -/
structure DisconnectedRelativeFamily (n r : ℕ) (order : Fin r → ℕ) where
  vertices : ℕ
  nonempty : 0 < vertices
  legs : Fin vertices → ℕ
  roots : Fin vertices → ℕ
  genus : Fin vertices → ℕ
  legLabels : Fin n ≃ (Σ v : Fin vertices, Fin (legs v))
  rootLabels : Fin r ≃ (Σ v : Fin vertices, Fin (roots v))
  target : ExpandedFamily P R S T
  maps : ∀ v : Fin vertices,
    RelativeMapOn P R S T target (legs v) (roots v) (genus v)
      (fun i => order (rootLabels.symm ⟨v, i⟩))

def disconnectedEvaluation {n r : ℕ} {order : Fin r → ℕ}
    (F : DisconnectedRelativeFamily P R S T n r order) (i : Fin r) : T ⟶ P.divisor :=
  rootEvaluation P R S T (F.maps (F.rootLabels i).1) (F.rootLabels i).2

/-- Combined automorphisms use one common target automorphism. Stability
does not require each disconnected component to stabilize the unused tails. -/
structure DisconnectedGeometricAutomorphism {n r : ℕ} {order : Fin r → ℕ}
    (F : DisconnectedRelativeFamily P R S T n r order)
    (Ω : Type) [Field Ω] (x : Spec (.of Ω) ⟶ T.left) where
  component : ∀ v : Fin F.vertices, GeometricAutomorphism P R S T (F.maps v) Ω x
  commonTarget : ∀ v w : Fin F.vertices, (component v).target = (component w).target

def IsStableDisconnected {n r : ℕ} {order : Fin r → ℕ}
    (F : DisconnectedRelativeFamily P R S T n r order) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T.left),
    Finite (DisconnectedGeometricAutomorphism P R S T F Ω x)

def contractedFamily {F : ExpandedFamily P R S T} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S T F n r g order) :
    GeneralStableMapFamilies.Family P.target.hom (n + r) g T.left T.hom where
  curve := f.curve
  map := f.map ≫ F.contraction.left
  over := by
    rw [Category.assoc, Over.w F.contraction]
    rw [← Over.w F.projection, ← Category.assoc, f.over]

structure MapReindex {T U : Over (Spec (.of k))} (h : T ⟶ U)
    {F : ExpandedFamily P R S U} {n r g : ℕ} {order : Fin r → ℕ}
    (f : RelativeMapOn P R S U F n r g order) (E : ExpandedReindex P R S h F) where
  family : RelativeMapOn P R S T E.family n r g order
  sourceMap : family.curve.X ⟶ f.curve.X
  cartesian : IsPullback sourceMap family.curve.π f.curve.π h.left
  marking : ∀ i : Fin (n + r), family.curve.marking i ≫ sourceMap = h.left ≫ f.curve.marking i
  map : family.map ≫ E.comparison.hom.left ≫ (pullback.fst F.projection h).left = sourceMap ≫ f.map
  evaluation : ∀ i : Fin r, rootEvaluation P R S T family i = h ≫ rootEvaluation P R S U f i

end MathlibExt.AlgebraicGeometry.RelativeExpandedMapFamilies
