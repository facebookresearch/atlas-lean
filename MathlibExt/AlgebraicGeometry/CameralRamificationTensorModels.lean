/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRootSL2Sources
public import MathlibExt.AlgebraicGeometry.CameralRamificationReindexing
public import MathlibExt.AlgebraicGeometry.NormalizedTorsorOperations

/-!
# Actual coroot ramification torsors and combined Weyl pullbacks

Each root torsor is the actual coroot pushout of frames of the computed
ramification dual. R_w is the finite tensor product over positive Lie
roots made negative by w. Positivity is membership in the actual Borel
subalgebra. The tensor is the actual inverse-diagonal fppf quotient.

The combined w pullback is the native cameral-scheme pullback followed
by pushout along w inverse acting on T. Its total scheme comparison is
fixed on every actual pushout point. Tensor, composition and unit maps
retain their actual maps back to the original torsors.

Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5.2--5.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralRamificationTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open ExpansionParameterModels ContractedTorsorModels NormalizedTorsorOperations

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]

abbrev Torus := torusScheme ℂ F.rank
abbrev Multiplicative := torusScheme ℂ 1

@[instance_reducible] def torusGroup : GrpObj (Torus F) := (tori F.rank).group

attribute [local instance] torusGroup

structure RootTorsorInputs (K : RootNormalizerGeometry G tori F) where
  torus : TensorCalculus (Torus F)
  multiplicative : letI := (tori 1).group; TensorCalculus Multiplicative
  coroot : ∀ i, letI := (tori 1).group; letI := K.corootHom i
    PushoutFunctor (Multiplicative) (Torus F) (F.roots.coroot i)
  character : ∀ i, letI := (tori 1).group; letI := K.characterHom i
    PushoutFunctor (Torus F) (Multiplicative) (F.roots.character i)
  weyl : ∀ w, letI := K.actionHom w⁻¹
    PushoutFunctor (Torus F) (Torus F) (F.roots.action w⁻¹).asIso.hom

variable {X : Over (Spec (.of ℂ))} (K : RootNormalizerGeometry G tori F)
  (D : RootTorsorInputs F K) (C : Cover F X)

/-- The literal coroot pushout of the native ramification-line frame bundle. -/
def rootTorsor (i : Fin F.roots.count) : Bundle (Torus F) (total F C) := by
  letI := (tori 1).group
  letI := K.corootHom i
  exact (D.coroot i).map (total F C) |>.obj (frames F C i).bundle

def rootPushout (i : Fin F.roots.count) :
    letI := (tori 1).group
    letI := K.corootHom i
    Pushout (Torus F) (F.roots.coroot i) (frames F C i).bundle (rootTorsor F K D C i) := by
  letI := (tori 1).group
  letI := K.corootHom i
  exact (D.coroot i).diagram (total F C) (frames F C i).bundle

def inversionRoots (w : F.Weyl) : List (Fin F.roots.count) := by
  classical
  exact (List.finRange F.roots.count).filter fun i =>
    decide (PositiveRoot G tori F i ∧ ¬ PositiveRoot G tori F (K.permutations.index w i))

def ramificationProduct : List (Fin F.roots.count) → Bundle (Torus F) (total F C)
  | [] => (D.torus.unit (total F C)).bundle
  | i :: is => NormalizedTorsorOperations.tensorObj (G := Torus F) D.torus.tensor
      (rootTorsor F K D C i)
      (ramificationProduct is)

def ramificationTorsor (w : F.Weyl) : Bundle (Torus F) (total F C) :=
  ramificationProduct F K D C (inversionRoots F K w)

theorem inversionRoots_one : inversionRoots F K 1 = [] := by
  classical
  simp [inversionRoots]

theorem ramificationTorsor_one :
    ramificationTorsor F K D C 1 = (D.torus.unit (total F C)).bundle := by
  rw [ramificationTorsor, inversionRoots_one]
  rfl

def coverIso (w : F.Weyl) : total F C ≅ total F C :=
  (Over.map X.hom).mapIso (C.cover.action w).asIso

/-- Pull by w on the cameral scheme, then push the T action by w inverse. -/
def combinedFunctor (w : F.Weyl) :
    Bundle (Torus F) (total F C) ⥤ Bundle (Torus F) (total F C) := by
  letI := K.actionHom w⁻¹
  exact D.torus.baseChange.change (coverIso F C w).hom ⋙ (D.weyl w).map (total F C)

def combined (w : F.Weyl) (P : Bundle (Torus F) (total F C)) :=
  (combinedFunctor F K D C w).obj P

def pulledBundle (w : F.Weyl) (P : Bundle (Torus F) (total F C)) :=
  (D.torus.baseChange.change (coverIso F C w).hom).obj P

structure CombinedModel (w : F.Weyl) (P : Bundle (Torus F) (total F C)) where
  comparison : (combined F K D C w P).torsor.total ≅
    pullback P.torsor.projection (coverIso F C w).hom
  projection : comparison.hom ≫ pullback.snd P.torsor.projection (coverIso F C w).hom =
    (combined F K D C w P).torsor.projection
  pushout_points : ∀ (U : Over (Spec (.of ℂ)))
      (p : U ⟶ (pulledBundle F K D C w P).torsor.total) (t : U ⟶ Torus F),
    letI := K.actionHom w⁻¹
    CartesianMonoidalCategory.lift p t ≫
      ((D.weyl w).diagram (total F C) (pulledBundle F K D C w P)).quotient ≫
        comparison.hom ≫ pullback.fst P.torsor.projection (coverIso F C w).hom =
    CartesianMonoidalCategory.lift (t ≫ (F.roots.action w).asIso.hom)
      (p ≫ original (D.torus.baseChange.pullback (coverIso F C w).hom P)) ≫
        γ[Torus F,P.torsor.total]

def combinedOriginal {w : F.Weyl} {P : Bundle (Torus F) (total F C)}
    (M : CombinedModel F K D C w P) : (combined F K D C w P).torsor.total ⟶ P.torsor.total :=
  M.comparison.hom ≫ pullback.fst P.torsor.projection (coverIso F C w).hom

structure WeylCalculus where
  model : ∀ w P, CombinedModel F K D C w P
  tensor : ∀ w (P Q : Bundle (Torus F) (total F C)),
    combined F K D C w (NormalizedTorsorOperations.tensorObj (G := Torus F) D.torus.tensor P Q) ≅
      NormalizedTorsorOperations.tensorObj (G := Torus F) D.torus.tensor
        (combined F K D C w P) (combined F K D C w Q)
  tensor_points : ∀ w (P Q : Bundle (Torus F) (total F C)) (U : Over (Spec (.of ℂ)))
      (p : U ⟶ (combined F K D C w P).torsor.total)
      (q : U ⟶ (combined F K D C w Q).torsor.total)
      (h : p ≫ (combined F K D C w P).torsor.projection =
        q ≫ (combined F K D C w Q).torsor.projection)
      (h' : (p ≫ combinedOriginal F K D C (model w P)) ≫ P.torsor.projection =
        (q ≫ combinedOriginal F K D C (model w Q)) ≫ Q.torsor.projection),
    tensorPoint (D.torus.tensor.model (total F C)
      (combined F K D C w P) (combined F K D C w Q)) p q h ≫
      (tensor w P Q).inv.iso.hom ≫
        combinedOriginal F K D C
          (model w (NormalizedTorsorOperations.tensorObj (G := Torus F) D.torus.tensor P Q)) =
    tensorPoint (D.torus.tensor.model (total F C) P Q)
      (p ≫ combinedOriginal F K D C (model w P))
      (q ≫ combinedOriginal F K D C (model w Q)) h'
  unit : combinedFunctor F K D C 1 ≅ 𝟭 (Bundle (Torus F) (total F C))
  unit_points : ∀ P, (unit.hom.app P).iso.hom = combinedOriginal F K D C (model 1 P)
  composition : ∀ u v,
    combinedFunctor F K D C u ⋙ combinedFunctor F K D C v ≅ combinedFunctor F K D C (u * v)
  composition_points : ∀ u v P,
    ((composition u v).hom.app P).iso.hom ≫ combinedOriginal F K D C (model (u * v) P) =
      combinedOriginal F K D C (model v (combined F K D C u P)) ≫
        combinedOriginal F K D C (model u P)

end MathlibExt.AlgebraicGeometry.CameralRamificationTensorModels
