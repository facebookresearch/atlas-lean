/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Edgewise
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialDiagonal
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedExtraDegeneracyRev

/-!
# The rowwise edgewise resolution

The ordinary total décalage of a simplicial set has bidegree
`(p,q) ↦ X_(p+q+1)` and is augmented by the straight/right ordinal block.
Reversing the outer simplex direction makes its diagonal the opposite-first
edgewise subdivision, while leaving that augmentation pointwise unchanged.

The boundary extra degeneracy is not natural in the inner simplex variable.
Accordingly this module packages an ordinary extra degeneracy only after the
inner degree has been fixed.  It makes no global extra-degeneracy,
realization, weak-equivalence, topology, outer-bisimplicial, or Stage claim.
-/

@[expose] public section


open CategoryTheory Opposite Simplicial

universe u

namespace SSet

/-- Ordinal sum, curried on ordinary simplices. -/
private def edgewiseOrdinalSum :
    SimplexCategory ⥤ SimplexCategory ⥤ SimplexCategory where
  obj p :=
    { obj := fun q => AugmentedSimplexCategory.tensorObjOf p q
      map := fun f => AugmentedSimplexCategory.tensorHomOf (𝟙 p) f
      map_id := by
        intro q
        exact AugmentedSimplexCategory.tensor_id
          (WithInitial.of p) (WithInitial.of q)
      map_comp := by
        intro q r s f g
        have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
          (x₁ := WithInitial.of p) (y₁ := WithInitial.of p)
          (z₁ := WithInitial.of p) (x₂ := WithInitial.of q)
          (y₂ := WithInitial.of r) (z₂ := WithInitial.of s)
          (𝟙 p) f (𝟙 p) g
        change AugmentedSimplexCategory.tensorHomOf (𝟙 p) f ≫
            AugmentedSimplexCategory.tensorHomOf (𝟙 p) g =
          AugmentedSimplexCategory.tensorHomOf ((𝟙 p) ≫ 𝟙 p) (f ≫ g) at h
        simpa using h.symm }
  map {p r} f :=
    { app := fun q => AugmentedSimplexCategory.tensorHomOf f (𝟙 q)
      naturality := by
        intro q s g
        have h₁ := AugmentedSimplexCategory.tensorHom_comp_tensorHom
          (x₁ := WithInitial.of p) (y₁ := WithInitial.of p)
          (z₁ := WithInitial.of r) (x₂ := WithInitial.of q)
          (y₂ := WithInitial.of s) (z₂ := WithInitial.of s)
          (𝟙 p) g f (𝟙 s)
        have h₂ := AugmentedSimplexCategory.tensorHom_comp_tensorHom
          (x₁ := WithInitial.of p) (y₁ := WithInitial.of r)
          (z₁ := WithInitial.of r) (x₂ := WithInitial.of q)
          (y₂ := WithInitial.of q) (z₂ := WithInitial.of s)
          f (𝟙 q) (𝟙 r) g
        change AugmentedSimplexCategory.tensorHomOf (𝟙 p) g ≫
            AugmentedSimplexCategory.tensorHomOf f (𝟙 s) =
          AugmentedSimplexCategory.tensorHomOf ((𝟙 p) ≫ f) (g ≫ 𝟙 s) at h₁
        change AugmentedSimplexCategory.tensorHomOf f (𝟙 q) ≫
            AugmentedSimplexCategory.tensorHomOf (𝟙 r) g =
          AugmentedSimplexCategory.tensorHomOf (f ≫ 𝟙 r) ((𝟙 q) ≫ g) at h₂
        simpa using h₁.trans h₂.symm }
  map_id := by
    intro p
    apply NatTrans.ext
    funext q
    exact AugmentedSimplexCategory.tensor_id
      (WithInitial.of p) (WithInitial.of q)
  map_comp := by
    intro p r s f g
    apply NatTrans.ext
    funext q
    have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
      (x₁ := WithInitial.of p) (y₁ := WithInitial.of r)
      (z₁ := WithInitial.of s) (x₂ := WithInitial.of q)
      (y₂ := WithInitial.of q) (z₂ := WithInitial.of q)
      f (𝟙 q) g (𝟙 q)
    change AugmentedSimplexCategory.tensorHomOf f (𝟙 q) ≫
        AugmentedSimplexCategory.tensorHomOf g (𝟙 q) =
      AugmentedSimplexCategory.tensorHomOf (f ≫ g) ((𝟙 q) ≫ 𝟙 q) at h
    simpa using h.symm

/-- The unreversed total-décalage bisimplicial carrier. -/
private def edgewiseResolutionUnreversedLeft (X : SSet.{u}) :
    SimplicialObject SSet.{u} where
  obj p := (edgewiseOrdinalSum.obj p.unop).op ⋙ X
  map {p r} f :=
    Functor.whiskerRight (NatTrans.op (edgewiseOrdinalSum.map f.unop)) X
  map_id := by
    intro p
    ext q x
    change X.map (AugmentedSimplexCategory.tensorHomOf
      (𝟙 p.unop) (𝟙 q.unop)).op x = x
    rw [show AugmentedSimplexCategory.tensorHomOf
        (𝟙 p.unop) (𝟙 q.unop) = 𝟙 _ by
      exact AugmentedSimplexCategory.tensor_id
        (WithInitial.of p.unop) (WithInitial.of q.unop)]
    change X.map (𝟙 (op
      (AugmentedSimplexCategory.tensorObjOf p.unop q.unop))) x = x
    rw [X.map_id]
    rfl
  map_comp := by
    intro p r s f g
    ext q x
    change X.map (AugmentedSimplexCategory.tensorHomOf
        (g.unop ≫ f.unop) (𝟙 q.unop)).op x =
      (X.map (AugmentedSimplexCategory.tensorHomOf
          f.unop (𝟙 q.unop)).op ≫
        X.map (AugmentedSimplexCategory.tensorHomOf
          g.unop (𝟙 q.unop)).op) x
    rw [← X.map_comp]
    apply ConcreteCategory.congr_hom
    apply congrArg X.map
    apply Quiver.Hom.unop_inj
    exact (AugmentedSimplexCategory.tensorHom_comp_tensorHom
      (x₁ := WithInitial.of s.unop) (y₁ := WithInitial.of r.unop)
      (z₁ := WithInitial.of p.unop) (x₂ := WithInitial.of q.unop)
      (y₂ := WithInitial.of q.unop) (z₂ := WithInitial.of q.unop)
      g.unop (𝟙 q.unop) f.unop (𝟙 q.unop)).symm

/-- The unreversed total décalage, augmented by the straight/right block. -/
private def edgewiseResolutionUnreversed (X : SSet.{u}) :
    SimplicialObject.Augmented SSet.{u} where
  left := edgewiseResolutionUnreversedLeft X
  right := X
  hom :=
    { app := fun p =>
        { app := fun q =>
            X.map (AugmentedSimplexCategory.inr' p.unop q.unop).op
          naturality := by
            intro q r f
            change
              X.map (AugmentedSimplexCategory.tensorHomOf
                  (𝟙 p.unop) f.unop).op ≫
                  X.map (AugmentedSimplexCategory.inr'
                    p.unop r.unop).op =
                X.map (AugmentedSimplexCategory.inr'
                    p.unop q.unop).op ≫ X.map f
            rw [← X.map_comp, ← X.map_comp]
            apply congrArg X.map
            apply Quiver.Hom.unop_inj
            exact AugmentedSimplexCategory.inr_comp_tensorHom
              (x₁ := WithInitial.of p.unop)
              (y₁ := WithInitial.of p.unop)
              (x₂ := WithInitial.of r.unop)
              (y₂ := WithInitial.of q.unop)
              (𝟙 p.unop) f.unop }
      naturality := by
        intro p r f
        ext q x
        change
          (X.map (AugmentedSimplexCategory.tensorHomOf
              f.unop (𝟙 q.unop)).op ≫
            X.map (AugmentedSimplexCategory.inr'
              r.unop q.unop).op) x =
          X.map (AugmentedSimplexCategory.inr'
            p.unop q.unop).op x
        rw [← X.map_comp]
        apply ConcreteCategory.congr_hom
        apply congrArg X.map
        apply Quiver.Hom.unop_inj
        have h := AugmentedSimplexCategory.inr_comp_tensorHom
          (x₁ := WithInitial.of r.unop)
          (y₁ := WithInitial.of p.unop)
          (x₂ := WithInitial.of q.unop)
          (y₂ := WithInitial.of q.unop)
          f.unop (𝟙 q.unop)
        change AugmentedSimplexCategory.inr' r.unop q.unop ≫
            AugmentedSimplexCategory.tensorHomOf f.unop (𝟙 q.unop) =
          (𝟙 q.unop) ≫
            AugmentedSimplexCategory.inr' p.unop q.unop at h
        simpa using h }

/-- The reversed total décalage whose diagonal is edgewise subdivision. -/
noncomputable def edgewiseResolution (X : SSet.{u}) :
    SimplicialObject.Augmented SSet.{u} := by
  let ordinalSum : SimplexCategory ⥤ SimplexCategory ⥤ SimplexCategory :=
    { obj p :=
        { obj := fun q => AugmentedSimplexCategory.tensorObjOf p q
          map := fun f => AugmentedSimplexCategory.tensorHomOf (𝟙 p) f
          map_id := by
            intro q
            exact AugmentedSimplexCategory.tensor_id
              (WithInitial.of p) (WithInitial.of q)
          map_comp := by
            intro q r s f g
            have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
              (x₁ := WithInitial.of p) (y₁ := WithInitial.of p)
              (z₁ := WithInitial.of p) (x₂ := WithInitial.of q)
              (y₂ := WithInitial.of r) (z₂ := WithInitial.of s)
              (𝟙 p) f (𝟙 p) g
            change AugmentedSimplexCategory.tensorHomOf (𝟙 p) f ≫
                AugmentedSimplexCategory.tensorHomOf (𝟙 p) g =
              AugmentedSimplexCategory.tensorHomOf ((𝟙 p) ≫ 𝟙 p) (f ≫ g) at h
            simpa using h.symm }
      map {p r} f :=
        { app := fun q => AugmentedSimplexCategory.tensorHomOf f (𝟙 q)
          naturality := by
            intro q s g
            have h₁ := AugmentedSimplexCategory.tensorHom_comp_tensorHom
              (x₁ := WithInitial.of p) (y₁ := WithInitial.of p)
              (z₁ := WithInitial.of r) (x₂ := WithInitial.of q)
              (y₂ := WithInitial.of s) (z₂ := WithInitial.of s)
              (𝟙 p) g f (𝟙 s)
            have h₂ := AugmentedSimplexCategory.tensorHom_comp_tensorHom
              (x₁ := WithInitial.of p) (y₁ := WithInitial.of r)
              (z₁ := WithInitial.of r) (x₂ := WithInitial.of q)
              (y₂ := WithInitial.of q) (z₂ := WithInitial.of s)
              f (𝟙 q) (𝟙 r) g
            change AugmentedSimplexCategory.tensorHomOf (𝟙 p) g ≫
                AugmentedSimplexCategory.tensorHomOf f (𝟙 s) =
              AugmentedSimplexCategory.tensorHomOf ((𝟙 p) ≫ f) (g ≫ 𝟙 s) at h₁
            change AugmentedSimplexCategory.tensorHomOf f (𝟙 q) ≫
                AugmentedSimplexCategory.tensorHomOf (𝟙 r) g =
              AugmentedSimplexCategory.tensorHomOf (f ≫ 𝟙 r) ((𝟙 q) ≫ g) at h₂
            simpa using h₁.trans h₂.symm }
      map_id := by
        intro p
        apply NatTrans.ext
        funext q
        exact AugmentedSimplexCategory.tensor_id
          (WithInitial.of p) (WithInitial.of q)
      map_comp := by
        intro p r s f g
        apply NatTrans.ext
        funext q
        have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
          (x₁ := WithInitial.of p) (y₁ := WithInitial.of r)
          (z₁ := WithInitial.of s) (x₂ := WithInitial.of q)
          (y₂ := WithInitial.of q) (z₂ := WithInitial.of q)
          f (𝟙 q) g (𝟙 q)
        change AugmentedSimplexCategory.tensorHomOf f (𝟙 q) ≫
            AugmentedSimplexCategory.tensorHomOf g (𝟙 q) =
          AugmentedSimplexCategory.tensorHomOf (f ≫ g) ((𝟙 q) ≫ 𝟙 q) at h
        simpa using h.symm
    }
  let unreversedLeft : SimplicialObject SSet.{u} :=
    { obj p := (ordinalSum.obj p.unop).op ⋙ X
      map {p r} f :=
        Functor.whiskerRight (NatTrans.op (ordinalSum.map f.unop)) X
      map_id := by
        intro p
        ext q x
        change X.map (AugmentedSimplexCategory.tensorHomOf
          (𝟙 p.unop) (𝟙 q.unop)).op x = x
        rw [show AugmentedSimplexCategory.tensorHomOf
            (𝟙 p.unop) (𝟙 q.unop) = 𝟙 _ by
          exact AugmentedSimplexCategory.tensor_id
            (WithInitial.of p.unop) (WithInitial.of q.unop)]
        change X.map (𝟙 (op
          (AugmentedSimplexCategory.tensorObjOf p.unop q.unop))) x = x
        rw [X.map_id]
        rfl
      map_comp := by
        intro p r s f g
        ext q x
        change X.map (AugmentedSimplexCategory.tensorHomOf
            (g.unop ≫ f.unop) (𝟙 q.unop)).op x =
          (X.map (AugmentedSimplexCategory.tensorHomOf
              f.unop (𝟙 q.unop)).op ≫
            X.map (AugmentedSimplexCategory.tensorHomOf
              g.unop (𝟙 q.unop)).op) x
        rw [← X.map_comp]
        apply ConcreteCategory.congr_hom
        apply congrArg X.map
        apply Quiver.Hom.unop_inj
        exact (AugmentedSimplexCategory.tensorHom_comp_tensorHom
          (x₁ := WithInitial.of s.unop) (y₁ := WithInitial.of r.unop)
          (z₁ := WithInitial.of p.unop) (x₂ := WithInitial.of q.unop)
          (y₂ := WithInitial.of q.unop) (z₂ := WithInitial.of q.unop)
          g.unop (𝟙 q.unop) f.unop (𝟙 q.unop)).symm
    }
  let unreversed : SimplicialObject.Augmented SSet.{u} :=
    { left := unreversedLeft
      right := X
      hom :=
        { app := fun p =>
            { app := fun q =>
                X.map (AugmentedSimplexCategory.inr' p.unop q.unop).op
              naturality := by
                intro q r f
                change
                  X.map (AugmentedSimplexCategory.tensorHomOf
                      (𝟙 p.unop) f.unop).op ≫
                      X.map (AugmentedSimplexCategory.inr'
                        p.unop r.unop).op =
                    X.map (AugmentedSimplexCategory.inr'
                        p.unop q.unop).op ≫ X.map f
                rw [← X.map_comp, ← X.map_comp]
                apply congrArg X.map
                apply Quiver.Hom.unop_inj
                exact AugmentedSimplexCategory.inr_comp_tensorHom
                  (x₁ := WithInitial.of p.unop)
                  (y₁ := WithInitial.of p.unop)
                  (x₂ := WithInitial.of r.unop)
                  (y₂ := WithInitial.of q.unop)
                  (𝟙 p.unop) f.unop }
          naturality := by
            intro p r f
            ext q x
            change
              (X.map (AugmentedSimplexCategory.tensorHomOf
                  f.unop (𝟙 q.unop)).op ≫
                X.map (AugmentedSimplexCategory.inr'
                  r.unop q.unop).op) x =
              X.map (AugmentedSimplexCategory.inr'
                p.unop q.unop).op x
            rw [← X.map_comp]
            apply ConcreteCategory.congr_hom
            apply congrArg X.map
            apply Quiver.Hom.unop_inj
            have h := AugmentedSimplexCategory.inr_comp_tensorHom
              (x₁ := WithInitial.of r.unop)
              (y₁ := WithInitial.of p.unop)
              (x₂ := WithInitial.of q.unop)
              (y₂ := WithInitial.of q.unop)
              f.unop (𝟙 q.unop)
            change AugmentedSimplexCategory.inr' r.unop q.unop ≫
                AugmentedSimplexCategory.tensorHomOf f.unop (𝟙 q.unop) =
              (𝟙 q.unop) ≫
                AugmentedSimplexCategory.inr' p.unop q.unop at h
            simpa using h }
    }
  exact SimplicialObject.Augmented.rev unreversed

/-- Bidegree computation for the reversed total décalage. -/
@[simp]
theorem edgewiseResolution_left_obj_obj (X : SSet.{u})
    (p q : SimplexCategoryᵒᵖ) :
    ((edgewiseResolution X).left.obj p).obj q =
      X.obj (op (AugmentedSimplexCategory.tensorObjOf p.unop q.unop)) := by
  change
    ((SimplicialObject.opFunctor.obj
      (edgewiseResolutionUnreversed X).left).obj p).obj q = _
  rfl

/-- The inner simplex variable acts on the straight/right ordinal block. -/
@[simp]
theorem edgewiseResolution_left_obj_map (X : SSet.{u})
    (p : SimplexCategoryᵒᵖ) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    ((edgewiseResolution X).left.obj p).map f =
      X.map (AugmentedSimplexCategory.tensorHomOf
        (𝟙 p.unop) f.unop).op := by
  change (((SimplicialObject.opFunctor.obj
    (edgewiseResolutionUnreversed X).left).obj p).map f) = _
  rfl

/-- The outer simplex variable acts through reversal on the first ordinal
block. -/
@[simp]
theorem edgewiseResolution_left_map_app (X : SSet.{u})
    {p r : SimplexCategoryᵒᵖ} (f : p ⟶ r)
    (q : SimplexCategoryᵒᵖ) :
    ((edgewiseResolution X).left.map f).app q =
      X.map (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.rev.map f.unop) (𝟙 q.unop)).op := by
  change (((SimplicialObject.Augmented.rev
    (edgewiseResolutionUnreversed X)).left.map f).app q) = _
  rw [SimplicialObject.Augmented.rev_left_map]
  rfl

/-- The reversed resolution retains the literal right-block augmentation. -/
@[simp]
theorem edgewiseResolution_hom_app_app (X : SSet.{u})
    (p q : SimplexCategoryᵒᵖ) :
    ((edgewiseResolution X).hom.app p).app q =
      X.map (AugmentedSimplexCategory.inr' p.unop q.unop).op := by
  change ((SimplicialObject.Augmented.rev
    (edgewiseResolutionUnreversed X)).hom.app p).app q = _
  rw [SimplicialObject.Augmented.rev_hom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal of the reversed total décalage is edgewise subdivision.
Every component is the identity. -/
noncomputable def edgewiseResolutionDiagonalIso (X : SSet.{u}) :
    simplicialDiagonalFunctor.obj (edgewiseResolution X).left ≅
      esd.obj X :=
  NatIso.ofComponents (fun p => by
    change X.obj (op (AugmentedSimplexCategory.tensorObjOf
      p.unop p.unop)) ≅ X.obj (op
        (AugmentedSimplexCategory.tensorObjOf p.unop p.unop))
    exact Iso.refl _) (by
    intro p r f
    let a : AugmentedSimplexCategory.tensorObjOf p.unop r.unop ⟶
        AugmentedSimplexCategory.tensorObjOf p.unop p.unop :=
      AugmentedSimplexCategory.tensorHomOf (𝟙 p.unop) f.unop
    let b : AugmentedSimplexCategory.tensorObjOf r.unop r.unop ⟶
        AugmentedSimplexCategory.tensorObjOf p.unop r.unop :=
      AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.rev.map f.unop) (𝟙 r.unop)
    have h := AugmentedSimplexCategory.tensorHom_comp_tensorHom
      (x₁ := WithInitial.of (SimplexCategory.rev.obj r.unop))
      (y₁ := WithInitial.of (SimplexCategory.rev.obj p.unop))
      (z₁ := WithInitial.of (SimplexCategory.rev.obj p.unop))
      (x₂ := WithInitial.of r.unop) (y₂ := WithInitial.of r.unop)
      (z₂ := WithInitial.of p.unop)
      (SimplexCategory.rev.map f.unop) (𝟙 r.unop)
      (𝟙 p.unop) f.unop
    change AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.rev.map f.unop) (𝟙 r.unop) ≫
          AugmentedSimplexCategory.tensorHomOf (𝟙 p.unop) f.unop =
      AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.rev.map f.unop ≫ 𝟙 p.unop)
        ((𝟙 r.unop) ≫ f.unop) at h
    have hTensor : b ≫ a = SimplexCategory.edgewiseQ.map f.unop := by
      change AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.rev.map f.unop) (𝟙 r.unop) ≫
          AugmentedSimplexCategory.tensorHomOf (𝟙 p.unop) f.unop =
        SimplexCategory.edgewiseQ.map f.unop
      rw [SimplexCategory.edgewiseQ_map]
      simpa using h
    have hOp : a.op ≫ b.op =
        (SimplexCategory.edgewiseQ.map f.unop).op := by
      apply Quiver.Hom.unop_inj
      exact hTensor
    have hMap : X.map a.op ≫ X.map b.op =
        X.map (SimplexCategory.edgewiseQ.map f.unop).op := by
      calc
        X.map a.op ≫ X.map b.op = X.map (a.op ≫ b.op) :=
          (X.map_comp a.op b.op).symm
        _ = X.map (SimplexCategory.edgewiseQ.map f.unop).op :=
          congrArg X.map hOp
    change
      ((edgewiseResolution X).left.obj p).map f ≫
          ((edgewiseResolution X).left.map f).app r =
        X.map (SimplexCategory.edgewiseQ.op.map f)
    rw [edgewiseResolution_left_obj_map,
      edgewiseResolution_left_map_app]
    exact hMap)

/-- The componentwise identity maps underlying the diagonal comparison. -/
@[simp]
theorem edgewiseResolutionDiagonalIso_hom_app (X : SSet.{u})
    (p : SimplexCategoryᵒᵖ) :
    (edgewiseResolutionDiagonalIso X).hom.app p =
      𝟙 (X.obj (op
        (AugmentedSimplexCategory.tensorObjOf p.unop p.unop))) :=
  rfl

/-- The inverse diagonal comparison also has identity components. -/
@[simp]
theorem edgewiseResolutionDiagonalIso_inv_app (X : SSet.{u})
    (p : SimplexCategoryᵒᵖ) :
    (edgewiseResolutionDiagonalIso X).inv.app p =
      𝟙 (X.obj (op
        (AugmentedSimplexCategory.tensorObjOf p.unop p.unop))) :=
  rfl

/-- The diagonal augmentation is exactly the raw right-block edgewise
comparison. -/
theorem edgewiseResolution_diagonal_augmentation (X : SSet.{u}) :
    (edgewiseResolutionDiagonalIso X).hom ≫ esdComparison.app X =
      simplicialDiagonalFunctor.map (edgewiseResolution X).hom ≫
        (diagonalConstIso X).hom := by
  ext p x
  rfl

/-- The codegeneracy at the boundary between an outer simplex of degree `n`
and a fixed inner simplex of degree `m`. -/
def edgewiseBoundaryDegeneracy (n m : ℕ) :
    AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌ ⟶
      AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌ :=
  let i : Fin ((AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌).len + 1) :=
    ⟨n + 1, by
      change n + 1 < n + m + 1 + 1
      omega⟩
  SimplexCategory.Hom.mk
    (i.predAboveOrderHom.comp
      (Fin.castOrderIso (by
        change ((n + 1) + m + 1) + 1 = ((n + m + 1) + 1) + 1
        omega)).toOrderEmbedding.toOrderHom)

/-- The section codegeneracy for a fixed inner simplex degree. -/
def edgewiseBoundarySection (m : ℕ) :
    AugmentedSimplexCategory.tensorObjOf ⦋0⦌ ⦋m⦌ ⟶ ⦋m⦌ :=
  SimplexCategory.Hom.mk
    ((0 : Fin (m + 1)).predAboveOrderHom.comp
      (Fin.castOrderIso (by
        change (0 + m + 1) + 1 = (m + 1) + 1
        omega)).toOrderEmbedding.toOrderHom)

@[simp]
private theorem edgewiseBoundarySection_inl (m : ℕ) :
    (edgewiseBoundarySection m).toOrderHom
        ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0) = 0 := by
  unfold edgewiseBoundarySection
  let e : (AugmentedSimplexCategory.tensorObjOf ⦋0⦌ ⦋m⦌).len + 1 =
      (m + 1) + 1 := by
    change (0 + m + 1) + 1 = (m + 1) + 1
    omega
  change (0 : Fin (m + 1)).predAbove
    (Fin.cast e
      ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0)) = 0
  have hx : Fin.cast e
      ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0) = 0 := by
    apply Fin.ext
    rw [AugmentedSimplexCategory.inl'_eval]
    rfl
  rw [hx]
  exact Fin.predAbove_right_zero

@[simp]
private theorem edgewiseBoundarySection_inr (m : ℕ)
    (j : Fin (m + 1)) :
    (edgewiseBoundarySection m).toOrderHom
        ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j) = j := by
  simp [edgewiseBoundarySection,
    AugmentedSimplexCategory.inr'_eval, Fin.predAbove]

@[simp]
private theorem edgewiseBoundaryDegeneracy_inr (n m : ℕ)
    (j : Fin (m + 1)) :
    (edgewiseBoundaryDegeneracy n m).toOrderHom
        ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j := by
  unfold edgewiseBoundaryDegeneracy
  let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
      n + m + 2 + 1 := by
    change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
    omega
  change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
      (Fin.cast e
        ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j)) =
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
  let y := (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
  have hx : Fin.cast e
      ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) = y.succ := by
    apply Fin.ext
    simp [y, AugmentedSimplexCategory.inr'_eval]
    omega
  have hle : (⟨n + 1, by omega⟩ : Fin (n + m + 2)) ≤ y := by
    rw [Fin.le_iff_val_le_val]
    simp [y, AugmentedSimplexCategory.inr'_eval]
  rw [hx, Fin.predAbove_succ_of_le _ _ hle]

@[simp]
private theorem edgewiseBoundaryDegeneracy_inl_castSucc (n m : ℕ)
    (j : Fin (n + 1)) :
    (edgewiseBoundaryDegeneracy n m).toOrderHom
        ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
      (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j := by
  unfold edgewiseBoundaryDegeneracy
  let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
      n + m + 2 + 1 := by
    change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
    omega
  change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
      (Fin.cast e
        ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc)) =
    (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
  let y := (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
  have hx : Fin.cast e
      ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
        y.castSucc := by
    apply Fin.ext
    simp [y, AugmentedSimplexCategory.inl'_eval]
  have hle : y ≤ (⟨n + 1, by omega⟩ : Fin (n + m + 2)) := by
    rw [Fin.le_iff_val_le_val]
    simp [y, AugmentedSimplexCategory.inl'_eval]
  rw [hx, Fin.predAbove_castSucc_of_le _ _ hle]

@[simp]
private theorem edgewiseBoundaryDegeneracy_inl_last (n m : ℕ) :
    (edgewiseBoundaryDegeneracy n m).toOrderHom
        ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
          (Fin.last (n + 1))) =
      (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 := by
  unfold edgewiseBoundaryDegeneracy
  let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
      n + m + 2 + 1 := by
    change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
    omega
  change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
      (Fin.cast e
        ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
          (Fin.last (n + 1)))) =
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0
  let k : Fin (n + m + 2) := ⟨n + 1, by omega⟩
  have hx : Fin.cast e
      ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
        (Fin.last (n + 1))) = k.castSucc := by
    apply Fin.ext
    simp [k, AugmentedSimplexCategory.inl'_eval]
  have hy : (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 = k := by
    apply Fin.ext
    simp [k, AugmentedSimplexCategory.inr'_eval]
  rw [hx, hy]
  exact Fin.predAbove_castSucc_self k

private theorem inr_comp_edgewiseBoundarySection (m : ℕ) :
    AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
        edgewiseBoundarySection m = 𝟙 ⦋m⦌ := by
  ext i
  simp [edgewiseBoundarySection,
    AugmentedSimplexCategory.inr'_eval]

private theorem edgewise_δ_zero_comp_boundaryDegeneracy_zero (m : ℕ) :
    AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) ≫
      edgewiseBoundaryDegeneracy 0 m =
    edgewiseBoundarySection m ≫
      AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ := by
  apply AugmentedSimplexCategory.inclusion.map_injective
  refine AugmentedSimplexCategory.tensorObj_hom_ext
    (x := WithInitial.of ⦋0⦌) (y := WithInitial.of ⦋m⦌)
    (z := WithInitial.of
      (AugmentedSimplexCategory.tensorObjOf ⦋0⦌ ⦋m⦌)) _ _ ?_ ?_
  · change AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy 0 m) =
      AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ ≫
        (edgewiseBoundarySection m ≫
          AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌)
    ext j
    fin_cases j
    change ((edgewiseBoundaryDegeneracy 0 m).toOrderHom
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0))).val =
      ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom
        ((edgewiseBoundarySection m).toOrderHom
          ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0))).val
    have ht := AugmentedSimplexCategory.inl_comp_tensorHom
      (x₁ := WithInitial.of ⦋0⦌) (y₁ := WithInitial.of ⦋1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) =
      SimplexCategory.δ (0 : Fin 2) ≫
        AugmentedSimplexCategory.inl' ⦋1⦌ ⦋m⦌ at ht
    have ht0 := SimplexCategory.congr_toOrderHom_apply ht (0 : Fin 1)
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0) =
      (AugmentedSimplexCategory.inl' ⦋1⦌ ⦋m⦌).toOrderHom
        ((SimplexCategory.δ (0 : Fin 2)).toOrderHom 0) at ht0
    rw [ht0, edgewiseBoundarySection_inl]
    have hδ : (SimplexCategory.δ (0 : Fin 2)).toOrderHom 0 =
        Fin.last 1 := by decide
    rw [hδ, edgewiseBoundaryDegeneracy_inl_last]
  · change AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy 0 m) =
      AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
        (edgewiseBoundarySection m ≫
          AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌)
    ext j
    change ((edgewiseBoundaryDegeneracy 0 m).toOrderHom
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j))).val =
      ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom
        ((edgewiseBoundarySection m).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j))).val
    have ht := AugmentedSimplexCategory.inr_comp_tensorHom
      (x₁ := WithInitial.of ⦋0⦌) (y₁ := WithInitial.of ⦋1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) =
      (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋1⦌ ⦋m⦌ at ht
    have htj := SimplexCategory.congr_toOrderHom_apply ht j
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inr' ⦋1⦌ ⦋m⦌).toOrderHom j at htj
    rw [htj, edgewiseBoundaryDegeneracy_inr,
      edgewiseBoundarySection_inr]

private theorem edgewise_δ_last_comp_boundaryDegeneracy (n m : ℕ) :
    AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) ≫
      edgewiseBoundaryDegeneracy n m =
    𝟙 (AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌) := by
  apply AugmentedSimplexCategory.inclusion.map_injective
  refine AugmentedSimplexCategory.tensorObj_hom_ext
    (x := WithInitial.of ⦋n⦌) (y := WithInitial.of ⦋m⦌)
    (z := WithInitial.of
      (AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌)) _ _ ?_ ?_
  · change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy n m) =
      AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫ 𝟙 _
    ext j
    have ht := AugmentedSimplexCategory.inl_comp_tensorHom
      (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) =
      SimplexCategory.δ (Fin.last (n + 1)) ≫
        AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ at ht
    have htj := SimplexCategory.congr_toOrderHom_apply ht j
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
        ((SimplexCategory.δ (Fin.last (n + 1))).toOrderHom j) at htj
    change ((edgewiseBoundaryDegeneracy n m).toOrderHom
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j))).val =
      ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j).val
    rw [htj]
    have hδ : (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom j =
        j.castSucc := by
      simp [SimplexCategory.δ]
    rw [hδ, edgewiseBoundaryDegeneracy_inl_castSucc]
  · change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy n m) =
      AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫ 𝟙 _
    ext j
    have ht := AugmentedSimplexCategory.inr_comp_tensorHom
      (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) =
      (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at ht
    have htj := SimplexCategory.congr_toOrderHom_apply ht j
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j at htj
    change ((edgewiseBoundaryDegeneracy n m).toOrderHom
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j))).val =
      ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j).val
    rw [htj, edgewiseBoundaryDegeneracy_inr]

private theorem edgewise_δ_comp_boundaryDegeneracy
    (n m : ℕ) (i : Fin (n + 2)) :
    AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) ≫
      edgewiseBoundaryDegeneracy (n + 1) m =
    edgewiseBoundaryDegeneracy n m ≫
      AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ i) (𝟙 ⦋m⦌) := by
  apply AugmentedSimplexCategory.inclusion.map_injective
  refine AugmentedSimplexCategory.tensorObj_hom_ext
    (x := WithInitial.of ⦋n + 1⦌) (y := WithInitial.of ⦋m⦌)
    (z := WithInitial.of
      (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌)) _ _ ?_ ?_
  · change AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy (n + 1) m) =
      AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
        (edgewiseBoundaryDegeneracy n m ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌))
    ext j
    have htL := AugmentedSimplexCategory.inl_comp_tensorHom
      (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n + 2⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) =
      SimplexCategory.δ i.castSucc ≫
        AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ at htL
    have htR := AugmentedSimplexCategory.inl_comp_tensorHom
      (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ i) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i) (𝟙 ⦋m⦌) =
      SimplexCategory.δ i ≫
        AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ at htR
    cases j using Fin.lastCases with
    | last =>
        change ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                  (Fin.last (n + 1))))).val =
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
              ((edgewiseBoundaryDegeneracy n m).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                  (Fin.last (n + 1))))).val
        have hL := SimplexCategory.congr_toOrderHom_apply htL (Fin.last (n + 1))
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                (Fin.last (n + 1))) =
          (AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
            ((SimplexCategory.δ i.castSucc).toOrderHom
              (Fin.last (n + 1))) at hL
        have htRi := AugmentedSimplexCategory.inr_comp_tensorHom
          (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
          (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
          (SimplexCategory.δ i) (𝟙 ⦋m⦌)
        change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
            AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i) (𝟙 ⦋m⦌) =
          (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at htRi
        have hRi := SimplexCategory.congr_toOrderHom_apply htRi (0 : Fin (m + 1))
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0) =
          (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom 0 at hRi
        have hLast : (SimplexCategory.δ i.castSucc).toOrderHom
            (Fin.last (n + 1)) = Fin.last (n + 2) := by
          simp [SimplexCategory.δ]
        rw [hL, hLast, edgewiseBoundaryDegeneracy_inl_last,
          edgewiseBoundaryDegeneracy_inl_last, ← hRi]
    | cast j =>
        change ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                  j.castSucc))).val =
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
              ((edgewiseBoundaryDegeneracy n m).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                  j.castSucc))).val
        have hL := SimplexCategory.congr_toOrderHom_apply htL j.castSucc
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                j.castSucc) =
          (AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
            ((SimplexCategory.δ i.castSucc).toOrderHom j.castSucc) at hL
        have hR := SimplexCategory.congr_toOrderHom_apply htR j
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j) =
          (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
            ((SimplexCategory.δ i).toOrderHom j) at hR
        have hCast : (SimplexCategory.δ i.castSucc).toOrderHom j.castSucc =
            ((SimplexCategory.δ i).toOrderHom j).castSucc := by
          exact Fin.castSucc_succAbove_castSucc
        rw [hL, hCast, edgewiseBoundaryDegeneracy_inl_castSucc,
          edgewiseBoundaryDegeneracy_inl_castSucc, ← hR]
  · change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy (n + 1) m) =
      AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
        (edgewiseBoundaryDegeneracy n m ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌))
    ext j
    have htL := AugmentedSimplexCategory.inr_comp_tensorHom
      (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n + 2⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) =
      (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ at htL
    have htR := AugmentedSimplexCategory.inr_comp_tensorHom
      (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.δ i) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i) (𝟙 ⦋m⦌) =
      (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at htR
    have hL := SimplexCategory.congr_toOrderHom_apply htL j
    have hR := SimplexCategory.congr_toOrderHom_apply htR j
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j at hL
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j at hR
    change ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j))).val =
      ((AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
          ((edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j))).val
    rw [hL, edgewiseBoundaryDegeneracy_inr,
      edgewiseBoundaryDegeneracy_inr, ← hR]

private theorem edgewise_σ_comp_boundaryDegeneracy
    (n m : ℕ) (i : Fin (n + 1)) :
    AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) ≫
      edgewiseBoundaryDegeneracy n m =
    edgewiseBoundaryDegeneracy (n + 1) m ≫
      AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.σ i) (𝟙 ⦋m⦌) := by
  apply AugmentedSimplexCategory.inclusion.map_injective
  refine AugmentedSimplexCategory.tensorObj_hom_ext
    (x := WithInitial.of ⦋n + 2⦌) (y := WithInitial.of ⦋m⦌)
    (z := WithInitial.of
      (AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌)) _ _ ?_ ?_
  · change AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy n m) =
      AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ ≫
        (edgewiseBoundaryDegeneracy (n + 1) m ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌))
    ext j
    have htL := AugmentedSimplexCategory.inl_comp_tensorHom
      (x₁ := WithInitial.of ⦋n + 2⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) =
      SimplexCategory.σ i.castSucc ≫
        AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ at htL
    have htR := AugmentedSimplexCategory.inl_comp_tensorHom
      (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.σ i) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i) (𝟙 ⦋m⦌) =
      SimplexCategory.σ i ≫
        AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ at htR
    cases j using Fin.lastCases with
    | last =>
        change ((edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                  (Fin.last (n + 2))))).val =
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
              ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                  (Fin.last (n + 2))))).val
        have hL := SimplexCategory.congr_toOrderHom_apply htL (Fin.last (n + 2))
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                (Fin.last (n + 2))) =
          (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
            ((SimplexCategory.σ i.castSucc).toOrderHom
              (Fin.last (n + 2))) at hL
        have htRi := AugmentedSimplexCategory.inr_comp_tensorHom
          (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n⦌)
          (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
          (SimplexCategory.σ i) (𝟙 ⦋m⦌)
        change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
            AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i) (𝟙 ⦋m⦌) =
          (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ at htRi
        have hRi := SimplexCategory.congr_toOrderHom_apply htRi (0 : Fin (m + 1))
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom 0) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 at hRi
        have hLast : (SimplexCategory.σ i.castSucc).toOrderHom
            (Fin.last (n + 2)) = Fin.last (n + 1) := by
          simp [SimplexCategory.σ]
        rw [hL, hLast, edgewiseBoundaryDegeneracy_inl_last,
          edgewiseBoundaryDegeneracy_inl_last, ← hRi]
    | cast j =>
        change ((edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                  j.castSucc))).val =
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
              ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                  j.castSucc))).val
        have hL := SimplexCategory.congr_toOrderHom_apply htL j.castSucc
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                j.castSucc) =
          (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
            ((SimplexCategory.σ i.castSucc).toOrderHom j.castSucc) at hL
        have hR := SimplexCategory.congr_toOrderHom_apply htR j
        change (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
          (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom
            ((SimplexCategory.σ i).toOrderHom j) at hR
        have hCast : (SimplexCategory.σ i.castSucc).toOrderHom j.castSucc =
            ((SimplexCategory.σ i).toOrderHom j).castSucc := by
          exact Fin.castSucc_predAbove_castSucc i j
        rw [hL, hCast, edgewiseBoundaryDegeneracy_inl_castSucc,
          edgewiseBoundaryDegeneracy_inl_castSucc, ← hR]
  · change AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ ≫
        (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) ≫
            edgewiseBoundaryDegeneracy n m) =
      AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ ≫
        (edgewiseBoundaryDegeneracy (n + 1) m ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌))
    ext j
    have htL := AugmentedSimplexCategory.inr_comp_tensorHom
      (x₁ := WithInitial.of ⦋n + 2⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) =
      (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at htL
    have htR := AugmentedSimplexCategory.inr_comp_tensorHom
      (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n⦌)
      (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
      (SimplexCategory.σ i) (𝟙 ⦋m⦌)
    change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i) (𝟙 ⦋m⦌) =
      (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ at htR
    have hL := SimplexCategory.congr_toOrderHom_apply htL j
    have hR := SimplexCategory.congr_toOrderHom_apply htR j
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j at hL
    change (AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
          ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
      (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j at hR
    change ((edgewiseBoundaryDegeneracy n m).toOrderHom
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j))).val =
      ((AugmentedSimplexCategory.tensorHomOf
        (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
          ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j))).val
    rw [hL, edgewiseBoundaryDegeneracy_inr,
      edgewiseBoundaryDegeneracy_inr, ← hR]

/-- Fixing the inner simplex degree in the unreversed augmentation gives an
ordinary augmented simplicial object in types. -/
private noncomputable def edgewiseResolutionUnreversedRow
    (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented (Type u) where
  left := ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).obj
    (edgewiseResolutionUnreversed X).left).obj q
  right := X.obj q
  hom := ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).map
    (edgewiseResolutionUnreversed X).hom).app q

/-- A fixed-inner row of the unreversed resolution has the right-handed
boundary extra degeneracy.  This is deliberately not natural in the fixed
inner degree. -/
private noncomputable def edgewiseResolutionUnreversedRowRightExtraDegeneracy
    (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    (edgewiseResolutionUnreversedRow X q).RightExtraDegeneracy := by
  induction q using Opposite.rec with
  | _ q =>
      induction q using SimplexCategory.rec with
      | _ m =>
          exact
            { s' := X.map (edgewiseBoundarySection m).op
              s := fun n => X.map (edgewiseBoundaryDegeneracy n m).op
              s'_comp_ε := by
                change X.map (edgewiseBoundarySection m).op ≫
                    X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).op = 𝟙 _
                rw [← X.map_comp]
                have h : (edgewiseBoundarySection m).op ≫
                    (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).op = 𝟙 _ := by
                  apply Quiver.Hom.unop_inj
                  exact inr_comp_edgewiseBoundarySection m
                rw [h, X.map_id]
              s₀_comp_δ₀ := by
                change X.map (edgewiseBoundaryDegeneracy 0 m).op ≫
                    X.map (AugmentedSimplexCategory.tensorHomOf
                      (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).op =
                  X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).op ≫
                    X.map (edgewiseBoundarySection m).op
                rw [← X.map_comp, ← X.map_comp]
                apply congrArg X.map
                apply Quiver.Hom.unop_inj
                exact edgewise_δ_zero_comp_boundaryDegeneracy_zero m
              s_comp_δ_last := by
                intro n
                change X.map (edgewiseBoundaryDegeneracy n m).op ≫
                    X.map (AugmentedSimplexCategory.tensorHomOf
                      (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).op = 𝟙 _
                rw [← X.map_comp]
                have h : (edgewiseBoundaryDegeneracy n m).op ≫
                    (AugmentedSimplexCategory.tensorHomOf
                      (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).op = 𝟙 _ := by
                  apply Quiver.Hom.unop_inj
                  exact edgewise_δ_last_comp_boundaryDegeneracy n m
                rw [h, X.map_id]
              s_comp_δ := by
                intro n i
                change X.map (edgewiseBoundaryDegeneracy (n + 1) m).op ≫
                    X.map (AugmentedSimplexCategory.tensorHomOf
                      (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).op =
                  X.map (AugmentedSimplexCategory.tensorHomOf
                    (SimplexCategory.δ i) (𝟙 ⦋m⦌)).op ≫
                    X.map (edgewiseBoundaryDegeneracy n m).op
                rw [← X.map_comp, ← X.map_comp]
                apply congrArg X.map
                apply Quiver.Hom.unop_inj
                exact edgewise_δ_comp_boundaryDegeneracy n m i
              s_comp_σ := by
                intro n i
                change X.map (edgewiseBoundaryDegeneracy n m).op ≫
                    X.map (AugmentedSimplexCategory.tensorHomOf
                      (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).op =
                  X.map (AugmentedSimplexCategory.tensorHomOf
                    (SimplexCategory.σ i) (𝟙 ⦋m⦌)).op ≫
                    X.map (edgewiseBoundaryDegeneracy (n + 1) m).op
                rw [← X.map_comp, ← X.map_comp]
                apply congrArg X.map
                apply Quiver.Hom.unop_inj
                exact edgewise_σ_comp_boundaryDegeneracy n m i }

/-- The reversed fixed-inner row.  Unlike a global contraction in `SSet`,
this row admits an extra degeneracy because its inner degree is fixed. -/
noncomputable def edgewiseResolutionRow
    (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented (Type u) where
  left := ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).obj
    (edgewiseResolution X).left).obj q
  right := X.obj q
  hom := ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).map
    (edgewiseResolution X).hom).app q

/-- Every fixed-inner reversed row has an ordinary extra degeneracy.  There is
no global extra degeneracy in `SSet`: these structures are indexed by, and
not natural in, the inner simplex `q`. -/
noncomputable def edgewiseResolutionRowExtraDegeneracy
    (X : SSet.{u}) (q : SimplexCategoryᵒᵖ) :
    (edgewiseResolutionRow X q).ExtraDegeneracy := by
  have hSection (m : ℕ) :
      AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
          edgewiseBoundarySection m = 𝟙 ⦋m⦌ := by
    ext i
    simp [edgewiseBoundarySection,
      AugmentedSimplexCategory.inr'_eval]
  have hDeltaZero (m : ℕ) :
      AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) ≫
        edgewiseBoundaryDegeneracy 0 m =
      edgewiseBoundarySection m ≫
        AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ := by
    have hBoundarySectionInl (m : ℕ) :
        (edgewiseBoundarySection m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0) = 0 := by
      unfold edgewiseBoundarySection
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋0⦌ ⦋m⦌).len + 1 =
          (m + 1) + 1 := by
        change (0 + m + 1) + 1 = (m + 1) + 1
        omega
      change (0 : Fin (m + 1)).predAbove
        (Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0)) = 0
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0) = 0 := by
        apply Fin.ext
        rw [AugmentedSimplexCategory.inl'_eval]
        rfl
      rw [hx]
      exact Fin.predAbove_right_zero
    have hBoundarySectionInr (m : ℕ)
        (j : Fin (m + 1)) :
        (edgewiseBoundarySection m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j) = j := by
      simp [edgewiseBoundarySection,
        AugmentedSimplexCategory.inr'_eval, Fin.predAbove]
    have hBoundaryDegeneracyInr (n m : ℕ)
        (j : Fin (m + 1)) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j)) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      let y := (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) = y.succ := by
        apply Fin.ext
        simp [y, AugmentedSimplexCategory.inr'_eval]
        omega
      have hle : (⟨n + 1, by omega⟩ : Fin (n + m + 2)) ≤ y := by
        rw [Fin.le_iff_val_le_val]
        simp [y, AugmentedSimplexCategory.inr'_eval]
      rw [hx, Fin.predAbove_succ_of_le _ _ hle]
    have hBoundaryDegeneracyLast (n m : ℕ) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              (Fin.last (n + 1))) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              (Fin.last (n + 1)))) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0
      let k : Fin (n + m + 2) := ⟨n + 1, by omega⟩
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
            (Fin.last (n + 1))) = k.castSucc := by
        apply Fin.ext
        simp [k, AugmentedSimplexCategory.inl'_eval]
      have hy : (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 = k := by
        apply Fin.ext
        simp [k, AugmentedSimplexCategory.inr'_eval]
      rw [hx, hy]
      exact Fin.predAbove_castSucc_self k
    apply AugmentedSimplexCategory.inclusion.map_injective
    refine AugmentedSimplexCategory.tensorObj_hom_ext
      (x := WithInitial.of ⦋0⦌) (y := WithInitial.of ⦋m⦌)
      (z := WithInitial.of
        (AugmentedSimplexCategory.tensorObjOf ⦋0⦌ ⦋m⦌)) _ _ ?_ ?_
    · change AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy 0 m) =
        AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ ≫
          (edgewiseBoundarySection m ≫
            AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌)
      ext j
      fin_cases j
      change ((edgewiseBoundaryDegeneracy 0 m).toOrderHom
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0))).val =
        ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom
          ((edgewiseBoundarySection m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0))).val
      have ht := AugmentedSimplexCategory.inl_comp_tensorHom
        (x₁ := WithInitial.of ⦋0⦌) (y₁ := WithInitial.of ⦋1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) =
        SimplexCategory.δ (0 : Fin 2) ≫
          AugmentedSimplexCategory.inl' ⦋1⦌ ⦋m⦌ at ht
      have ht0 := SimplexCategory.congr_toOrderHom_apply ht (0 : Fin 1)
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋m⦌).toOrderHom 0) =
        (AugmentedSimplexCategory.inl' ⦋1⦌ ⦋m⦌).toOrderHom
          ((SimplexCategory.δ (0 : Fin 2)).toOrderHom 0) at ht0
      rw [ht0, hBoundarySectionInl]
      have hδ : (SimplexCategory.δ (0 : Fin 2)).toOrderHom 0 =
          Fin.last 1 := by decide
      rw [hδ, hBoundaryDegeneracyLast]
    · change AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy 0 m) =
        AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
          (edgewiseBoundarySection m ≫
            AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌)
      ext j
      change ((edgewiseBoundaryDegeneracy 0 m).toOrderHom
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j))).val =
        ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom
          ((edgewiseBoundarySection m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j))).val
      have ht := AugmentedSimplexCategory.inr_comp_tensorHom
        (x₁ := WithInitial.of ⦋0⦌) (y₁ := WithInitial.of ⦋1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌) =
        (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋1⦌ ⦋m⦌ at ht
      have htj := SimplexCategory.congr_toOrderHom_apply ht j
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).toOrderHom j) =
        (AugmentedSimplexCategory.inr' ⦋1⦌ ⦋m⦌).toOrderHom j at htj
      rw [htj, hBoundaryDegeneracyInr,
        hBoundarySectionInr]
  have hDeltaLast (n m : ℕ) :
      AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) ≫
        edgewiseBoundaryDegeneracy n m =
      𝟙 (AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌) := by
    have hBoundaryDegeneracyInr (n m : ℕ)
        (j : Fin (m + 1)) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j)) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      let y := (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) = y.succ := by
        apply Fin.ext
        simp [y, AugmentedSimplexCategory.inr'_eval]
        omega
      have hle : (⟨n + 1, by omega⟩ : Fin (n + m + 2)) ≤ y := by
        rw [Fin.le_iff_val_le_val]
        simp [y, AugmentedSimplexCategory.inr'_eval]
      rw [hx, Fin.predAbove_succ_of_le _ _ hle]
    have hBoundaryDegeneracyCastSucc (n m : ℕ)
        (j : Fin (n + 1)) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
          (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc)) =
        (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
      let y := (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
            y.castSucc := by
        apply Fin.ext
        simp [y, AugmentedSimplexCategory.inl'_eval]
      have hle : y ≤ (⟨n + 1, by omega⟩ : Fin (n + m + 2)) := by
        rw [Fin.le_iff_val_le_val]
        simp [y, AugmentedSimplexCategory.inl'_eval]
      rw [hx, Fin.predAbove_castSucc_of_le _ _ hle]
    apply AugmentedSimplexCategory.inclusion.map_injective
    refine AugmentedSimplexCategory.tensorObj_hom_ext
      (x := WithInitial.of ⦋n⦌) (y := WithInitial.of ⦋m⦌)
      (z := WithInitial.of
        (AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌)) _ _ ?_ ?_
    · change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy n m) =
        AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫ 𝟙 _
      ext j
      have ht := AugmentedSimplexCategory.inl_comp_tensorHom
        (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) =
        SimplexCategory.δ (Fin.last (n + 1)) ≫
          AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ at ht
      have htj := SimplexCategory.congr_toOrderHom_apply ht j
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j) =
        (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
          ((SimplexCategory.δ (Fin.last (n + 1))).toOrderHom j) at htj
      change ((edgewiseBoundaryDegeneracy n m).toOrderHom
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j))).val =
        ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j).val
      rw [htj]
      have hδ : (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom j =
          j.castSucc := by
        simp [SimplexCategory.δ]
      rw [hδ, hBoundaryDegeneracyCastSucc]
    · change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy n m) =
        AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫ 𝟙 _
      ext j
      have ht := AugmentedSimplexCategory.inr_comp_tensorHom
        (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌) =
        (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at ht
      have htj := SimplexCategory.congr_toOrderHom_apply ht j
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j) =
        (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j at htj
      change ((edgewiseBoundaryDegeneracy n m).toOrderHom
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j))).val =
        ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j).val
      rw [htj, hBoundaryDegeneracyInr]
  have hDelta
      (n m : ℕ) (i : Fin (n + 2)) :
      AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) ≫
        edgewiseBoundaryDegeneracy (n + 1) m =
      edgewiseBoundaryDegeneracy n m ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i) (𝟙 ⦋m⦌) := by
    have hBoundaryDegeneracyInr (n m : ℕ)
        (j : Fin (m + 1)) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j)) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      let y := (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) = y.succ := by
        apply Fin.ext
        simp [y, AugmentedSimplexCategory.inr'_eval]
        omega
      have hle : (⟨n + 1, by omega⟩ : Fin (n + m + 2)) ≤ y := by
        rw [Fin.le_iff_val_le_val]
        simp [y, AugmentedSimplexCategory.inr'_eval]
      rw [hx, Fin.predAbove_succ_of_le _ _ hle]
    have hBoundaryDegeneracyCastSucc (n m : ℕ)
        (j : Fin (n + 1)) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
          (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc)) =
        (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
      let y := (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
            y.castSucc := by
        apply Fin.ext
        simp [y, AugmentedSimplexCategory.inl'_eval]
      have hle : y ≤ (⟨n + 1, by omega⟩ : Fin (n + m + 2)) := by
        rw [Fin.le_iff_val_le_val]
        simp [y, AugmentedSimplexCategory.inl'_eval]
      rw [hx, Fin.predAbove_castSucc_of_le _ _ hle]
    have hBoundaryDegeneracyLast (n m : ℕ) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              (Fin.last (n + 1))) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              (Fin.last (n + 1)))) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0
      let k : Fin (n + m + 2) := ⟨n + 1, by omega⟩
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
            (Fin.last (n + 1))) = k.castSucc := by
        apply Fin.ext
        simp [k, AugmentedSimplexCategory.inl'_eval]
      have hy : (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 = k := by
        apply Fin.ext
        simp [k, AugmentedSimplexCategory.inr'_eval]
      rw [hx, hy]
      exact Fin.predAbove_castSucc_self k
    apply AugmentedSimplexCategory.inclusion.map_injective
    refine AugmentedSimplexCategory.tensorObj_hom_ext
      (x := WithInitial.of ⦋n + 1⦌) (y := WithInitial.of ⦋m⦌)
      (z := WithInitial.of
        (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌)) _ _ ?_ ?_
    · change AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy (n + 1) m) =
        AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
          (edgewiseBoundaryDegeneracy n m ≫
            AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i) (𝟙 ⦋m⦌))
      ext j
      have htL := AugmentedSimplexCategory.inl_comp_tensorHom
        (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n + 2⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) =
        SimplexCategory.δ i.castSucc ≫
          AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ at htL
      have htR := AugmentedSimplexCategory.inl_comp_tensorHom
        (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ i) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌) =
        SimplexCategory.δ i ≫
          AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ at htR
      cases j using Fin.lastCases with
      | last =>
          change ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
              ((AugmentedSimplexCategory.tensorHomOf
                (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                    (Fin.last (n + 1))))).val =
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
                ((edgewiseBoundaryDegeneracy n m).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                    (Fin.last (n + 1))))).val
          have hL := SimplexCategory.congr_toOrderHom_apply htL (Fin.last (n + 1))
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                  (Fin.last (n + 1))) =
            (AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
              ((SimplexCategory.δ i.castSucc).toOrderHom
                (Fin.last (n + 1))) at hL
          have htRi := AugmentedSimplexCategory.inr_comp_tensorHom
            (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
            (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
            (SimplexCategory.δ i) (𝟙 ⦋m⦌)
          change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
              AugmentedSimplexCategory.tensorHomOf
                (SimplexCategory.δ i) (𝟙 ⦋m⦌) =
            (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at htRi
          have hRi := SimplexCategory.congr_toOrderHom_apply htRi (0 : Fin (m + 1))
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0) =
            (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom 0 at hRi
          have hLast : (SimplexCategory.δ i.castSucc).toOrderHom
              (Fin.last (n + 1)) = Fin.last (n + 2) := by
            simp [SimplexCategory.δ]
          rw [hL, hLast, hBoundaryDegeneracyLast,
            hBoundaryDegeneracyLast, ← hRi]
      | cast j =>
          change ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
              ((AugmentedSimplexCategory.tensorHomOf
                (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                    j.castSucc))).val =
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
                ((edgewiseBoundaryDegeneracy n m).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                    j.castSucc))).val
          have hL := SimplexCategory.congr_toOrderHom_apply htL j.castSucc
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
                  j.castSucc) =
            (AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
              ((SimplexCategory.δ i.castSucc).toOrderHom j.castSucc) at hL
          have hR := SimplexCategory.congr_toOrderHom_apply htR j
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j) =
            (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              ((SimplexCategory.δ i).toOrderHom j) at hR
          have hCast : (SimplexCategory.δ i.castSucc).toOrderHom j.castSucc =
              ((SimplexCategory.δ i).toOrderHom j).castSucc := by
            exact Fin.castSucc_succAbove_castSucc
          rw [hL, hCast, hBoundaryDegeneracyCastSucc,
            hBoundaryDegeneracyCastSucc, ← hR]
    · change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy (n + 1) m) =
        AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
          (edgewiseBoundaryDegeneracy n m ≫
            AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.δ i) (𝟙 ⦋m⦌))
      ext j
      have htL := AugmentedSimplexCategory.inr_comp_tensorHom
        (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n + 2⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌) =
        (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ at htL
      have htR := AugmentedSimplexCategory.inr_comp_tensorHom
        (x₁ := WithInitial.of ⦋n⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.δ i) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i) (𝟙 ⦋m⦌) =
        (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at htR
      have hL := SimplexCategory.congr_toOrderHom_apply htL j
      have hR := SimplexCategory.congr_toOrderHom_apply htR j
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
        (AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j at hL
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j) =
        (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j at hR
      change ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j))).val =
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.δ i) (𝟙 ⦋m⦌)).toOrderHom
            ((edgewiseBoundaryDegeneracy n m).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j))).val
      rw [hL, hBoundaryDegeneracyInr,
        hBoundaryDegeneracyInr, ← hR]
  have hSigma
      (n m : ℕ) (i : Fin (n + 1)) :
      AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) ≫
        edgewiseBoundaryDegeneracy n m =
      edgewiseBoundaryDegeneracy (n + 1) m ≫
        AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i) (𝟙 ⦋m⦌) := by
    have hBoundaryDegeneracyInr (n m : ℕ)
        (j : Fin (m + 1)) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j)) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      let y := (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) = y.succ := by
        apply Fin.ext
        simp [y, AugmentedSimplexCategory.inr'_eval]
        omega
      have hle : (⟨n + 1, by omega⟩ : Fin (n + m + 2)) ≤ y := by
        rw [Fin.le_iff_val_le_val]
        simp [y, AugmentedSimplexCategory.inr'_eval]
      rw [hx, Fin.predAbove_succ_of_le _ _ hle]
    have hBoundaryDegeneracyCastSucc (n m : ℕ)
        (j : Fin (n + 1)) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
          (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc)) =
        (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
      let y := (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom j
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j.castSucc) =
            y.castSucc := by
        apply Fin.ext
        simp [y, AugmentedSimplexCategory.inl'_eval]
      have hle : y ≤ (⟨n + 1, by omega⟩ : Fin (n + m + 2)) := by
        rw [Fin.le_iff_val_le_val]
        simp [y, AugmentedSimplexCategory.inl'_eval]
      rw [hx, Fin.predAbove_castSucc_of_le _ _ hle]
    have hBoundaryDegeneracyLast (n m : ℕ) :
        (edgewiseBoundaryDegeneracy n m).toOrderHom
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              (Fin.last (n + 1))) =
          (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 := by
      unfold edgewiseBoundaryDegeneracy
      let e : (AugmentedSimplexCategory.tensorObjOf ⦋n + 1⦌ ⦋m⦌).len + 1 =
          n + m + 2 + 1 := by
        change ((n + 1) + m + 1) + 1 = n + m + 2 + 1
        omega
      change (⟨n + 1, by omega⟩ : Fin (n + m + 2)).predAbove
          (Fin.cast e
            ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              (Fin.last (n + 1)))) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0
      let k : Fin (n + m + 2) := ⟨n + 1, by omega⟩
      have hx : Fin.cast e
          ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
            (Fin.last (n + 1))) = k.castSucc := by
        apply Fin.ext
        simp [k, AugmentedSimplexCategory.inl'_eval]
      have hy : (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 = k := by
        apply Fin.ext
        simp [k, AugmentedSimplexCategory.inr'_eval]
      rw [hx, hy]
      exact Fin.predAbove_castSucc_self k
    apply AugmentedSimplexCategory.inclusion.map_injective
    refine AugmentedSimplexCategory.tensorObj_hom_ext
      (x := WithInitial.of ⦋n + 2⦌) (y := WithInitial.of ⦋m⦌)
      (z := WithInitial.of
        (AugmentedSimplexCategory.tensorObjOf ⦋n⦌ ⦋m⦌)) _ _ ?_ ?_
    · change AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy n m) =
        AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ ≫
          (edgewiseBoundaryDegeneracy (n + 1) m ≫
            AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i) (𝟙 ⦋m⦌))
      ext j
      have htL := AugmentedSimplexCategory.inl_comp_tensorHom
        (x₁ := WithInitial.of ⦋n + 2⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) =
        SimplexCategory.σ i.castSucc ≫
          AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ at htL
      have htR := AugmentedSimplexCategory.inl_comp_tensorHom
        (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.σ i) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌) =
        SimplexCategory.σ i ≫
          AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌ at htR
      cases j using Fin.lastCases with
      | last =>
          change ((edgewiseBoundaryDegeneracy n m).toOrderHom
              ((AugmentedSimplexCategory.tensorHomOf
                (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                    (Fin.last (n + 2))))).val =
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
                ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                    (Fin.last (n + 2))))).val
          have hL := SimplexCategory.congr_toOrderHom_apply htL (Fin.last (n + 2))
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                  (Fin.last (n + 2))) =
            (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              ((SimplexCategory.σ i.castSucc).toOrderHom
                (Fin.last (n + 2))) at hL
          have htRi := AugmentedSimplexCategory.inr_comp_tensorHom
            (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n⦌)
            (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
            (SimplexCategory.σ i) (𝟙 ⦋m⦌)
          change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
              AugmentedSimplexCategory.tensorHomOf
                (SimplexCategory.σ i) (𝟙 ⦋m⦌) =
            (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ at htRi
          have hRi := SimplexCategory.congr_toOrderHom_apply htRi (0 : Fin (m + 1))
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom 0) =
            (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom 0 at hRi
          have hLast : (SimplexCategory.σ i.castSucc).toOrderHom
              (Fin.last (n + 2)) = Fin.last (n + 1) := by
            simp [SimplexCategory.σ]
          rw [hL, hLast, hBoundaryDegeneracyLast,
            hBoundaryDegeneracyLast, ← hRi]
      | cast j =>
          change ((edgewiseBoundaryDegeneracy n m).toOrderHom
              ((AugmentedSimplexCategory.tensorHomOf
                (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                    j.castSucc))).val =
            ((AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
                ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
                  ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                    j.castSucc))).val
          have hL := SimplexCategory.congr_toOrderHom_apply htL j.castSucc
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 2⦌ ⦋m⦌).toOrderHom
                  j.castSucc) =
            (AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom
              ((SimplexCategory.σ i.castSucc).toOrderHom j.castSucc) at hL
          have hR := SimplexCategory.congr_toOrderHom_apply htR j
          change (AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
                ((AugmentedSimplexCategory.inl' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
            (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋m⦌).toOrderHom
              ((SimplexCategory.σ i).toOrderHom j) at hR
          have hCast : (SimplexCategory.σ i.castSucc).toOrderHom j.castSucc =
              ((SimplexCategory.σ i).toOrderHom j).castSucc := by
            exact Fin.castSucc_predAbove_castSucc i j
          rw [hL, hCast, hBoundaryDegeneracyCastSucc,
            hBoundaryDegeneracyCastSucc, ← hR]
    · change AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ ≫
          (AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) ≫
              edgewiseBoundaryDegeneracy n m) =
        AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ ≫
          (edgewiseBoundaryDegeneracy (n + 1) m ≫
            AugmentedSimplexCategory.tensorHomOf
              (SimplexCategory.σ i) (𝟙 ⦋m⦌))
      ext j
      have htL := AugmentedSimplexCategory.inr_comp_tensorHom
        (x₁ := WithInitial.of ⦋n + 2⦌) (y₁ := WithInitial.of ⦋n + 1⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌) =
        (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ at htL
      have htR := AugmentedSimplexCategory.inr_comp_tensorHom
        (x₁ := WithInitial.of ⦋n + 1⦌) (y₁ := WithInitial.of ⦋n⦌)
        (x₂ := WithInitial.of ⦋m⦌) (y₂ := WithInitial.of ⦋m⦌)
        (SimplexCategory.σ i) (𝟙 ⦋m⦌)
      change AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌ ≫
          AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i) (𝟙 ⦋m⦌) =
        (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌ at htR
      have hL := SimplexCategory.congr_toOrderHom_apply htL j
      have hR := SimplexCategory.congr_toOrderHom_apply htR j
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j) =
        (AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j at hL
      change (AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
            ((AugmentedSimplexCategory.inr' ⦋n + 1⦌ ⦋m⦌).toOrderHom j) =
        (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋m⦌).toOrderHom j at hR
      change ((edgewiseBoundaryDegeneracy n m).toOrderHom
          ((AugmentedSimplexCategory.tensorHomOf
            (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j))).val =
        ((AugmentedSimplexCategory.tensorHomOf
          (SimplexCategory.σ i) (𝟙 ⦋m⦌)).toOrderHom
            ((edgewiseBoundaryDegeneracy (n + 1) m).toOrderHom
              ((AugmentedSimplexCategory.inr' ⦋n + 2⦌ ⦋m⦌).toOrderHom j))).val
      rw [hL, hBoundaryDegeneracyInr,
        hBoundaryDegeneracyInr, ← hR]
  induction q using Opposite.rec with
  | _ q =>
      induction q using SimplexCategory.rec with
      | _ m =>
          let row : SimplicialObject.Augmented (Type u) :=
            { left :=
                { obj := fun p => X.obj (op
                    (AugmentedSimplexCategory.tensorObjOf p.unop ⦋m⦌))
                  map {p r} f := X.map (AugmentedSimplexCategory.tensorHomOf
                    f.unop (𝟙 ⦋m⦌)).op
                  map_id := by
                    intro p
                    change X.map (AugmentedSimplexCategory.tensorHomOf
                      (𝟙 p.unop) (𝟙 ⦋m⦌)).op = 𝟙 _
                    rw [show AugmentedSimplexCategory.tensorHomOf
                        (𝟙 p.unop) (𝟙 ⦋m⦌) = 𝟙 _ by
                      exact AugmentedSimplexCategory.tensor_id
                        (WithInitial.of p.unop) (WithInitial.of ⦋m⦌)]
                    change X.map (𝟙 (op
                      (AugmentedSimplexCategory.tensorObjOf p.unop ⦋m⦌))) = 𝟙 _
                    exact X.map_id _
                  map_comp := by
                    intro p r s f g
                    change X.map (AugmentedSimplexCategory.tensorHomOf
                        (g.unop ≫ f.unop) (𝟙 ⦋m⦌)).op =
                      X.map (AugmentedSimplexCategory.tensorHomOf
                          f.unop (𝟙 ⦋m⦌)).op ≫
                        X.map (AugmentedSimplexCategory.tensorHomOf
                          g.unop (𝟙 ⦋m⦌)).op
                    rw [← X.map_comp]
                    apply congrArg X.map
                    apply Quiver.Hom.unop_inj
                    exact (AugmentedSimplexCategory.tensorHom_comp_tensorHom
                      (x₁ := WithInitial.of s.unop) (y₁ := WithInitial.of r.unop)
                      (z₁ := WithInitial.of p.unop) (x₂ := WithInitial.of ⦋m⦌)
                      (y₂ := WithInitial.of ⦋m⦌) (z₂ := WithInitial.of ⦋m⦌)
                      g.unop (𝟙 ⦋m⦌) f.unop (𝟙 ⦋m⦌)).symm }
              right := X.obj (op ⦋m⦌)
              hom :=
                { app := fun p => X.map
                    (AugmentedSimplexCategory.inr' p.unop ⦋m⦌).op
                  naturality := by
                    intro p r f
                    change X.map (AugmentedSimplexCategory.tensorHomOf
                        f.unop (𝟙 ⦋m⦌)).op ≫
                      X.map (AugmentedSimplexCategory.inr' r.unop ⦋m⦌).op =
                        X.map (AugmentedSimplexCategory.inr' p.unop ⦋m⦌).op
                    rw [← X.map_comp]
                    apply congrArg X.map
                    apply Quiver.Hom.unop_inj
                    have h := AugmentedSimplexCategory.inr_comp_tensorHom
                      (x₁ := WithInitial.of r.unop)
                      (y₁ := WithInitial.of p.unop)
                      (x₂ := WithInitial.of ⦋m⦌)
                      (y₂ := WithInitial.of ⦋m⦌)
                      f.unop (𝟙 ⦋m⦌)
                    change AugmentedSimplexCategory.inr' r.unop ⦋m⦌ ≫
                        AugmentedSimplexCategory.tensorHomOf f.unop (𝟙 ⦋m⦌) =
                      (𝟙 ⦋m⦌) ≫ AugmentedSimplexCategory.inr' p.unop ⦋m⦌ at h
                    simpa using h } }
          change (SimplicialObject.Augmented.rev row).ExtraDegeneracy
          exact SimplicialObject.Augmented.RightExtraDegeneracy.toExtraDegeneracyRev
            (show row.RightExtraDegeneracy from
              { s' := X.map (edgewiseBoundarySection m).op
                s := fun n => X.map (edgewiseBoundaryDegeneracy n m).op
                s'_comp_ε := by
                  change X.map (edgewiseBoundarySection m).op ≫
                      X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).op = 𝟙 _
                  rw [← X.map_comp]
                  have h : (edgewiseBoundarySection m).op ≫
                      (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).op = 𝟙 _ := by
                    apply Quiver.Hom.unop_inj
                    exact hSection m
                  rw [h, X.map_id]
                s₀_comp_δ₀ := by
                  change X.map (edgewiseBoundaryDegeneracy 0 m).op ≫
                      X.map (AugmentedSimplexCategory.tensorHomOf
                        (SimplexCategory.δ (0 : Fin 2)) (𝟙 ⦋m⦌)).op =
                    X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋m⦌).op ≫
                      X.map (edgewiseBoundarySection m).op
                  rw [← X.map_comp, ← X.map_comp]
                  apply congrArg X.map
                  apply Quiver.Hom.unop_inj
                  exact hDeltaZero m
                s_comp_δ_last := by
                  intro n
                  change X.map (edgewiseBoundaryDegeneracy n m).op ≫
                      X.map (AugmentedSimplexCategory.tensorHomOf
                        (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).op = 𝟙 _
                  rw [← X.map_comp]
                  have h : (edgewiseBoundaryDegeneracy n m).op ≫
                      (AugmentedSimplexCategory.tensorHomOf
                        (SimplexCategory.δ (Fin.last (n + 1))) (𝟙 ⦋m⦌)).op = 𝟙 _ := by
                    apply Quiver.Hom.unop_inj
                    exact hDeltaLast n m
                  rw [h, X.map_id]
                s_comp_δ := by
                  intro n i
                  change X.map (edgewiseBoundaryDegeneracy (n + 1) m).op ≫
                      X.map (AugmentedSimplexCategory.tensorHomOf
                        (SimplexCategory.δ i.castSucc) (𝟙 ⦋m⦌)).op =
                    X.map (AugmentedSimplexCategory.tensorHomOf
                      (SimplexCategory.δ i) (𝟙 ⦋m⦌)).op ≫
                      X.map (edgewiseBoundaryDegeneracy n m).op
                  rw [← X.map_comp, ← X.map_comp]
                  apply congrArg X.map
                  apply Quiver.Hom.unop_inj
                  exact hDelta n m i
                s_comp_σ := by
                  intro n i
                  change X.map (edgewiseBoundaryDegeneracy n m).op ≫
                      X.map (AugmentedSimplexCategory.tensorHomOf
                        (SimplexCategory.σ i.castSucc) (𝟙 ⦋m⦌)).op =
                    X.map (AugmentedSimplexCategory.tensorHomOf
                      (SimplexCategory.σ i) (𝟙 ⦋m⦌)).op ≫
                      X.map (edgewiseBoundaryDegeneracy (n + 1) m).op
                  rw [← X.map_comp, ← X.map_comp]
                  apply congrArg X.map
                  apply Quiver.Hom.unop_inj
                  exact hSigma n m i })

/-- The fixed-row section is induced by the boundary codegeneracy `σ 0`. -/
@[simp]
theorem edgewiseResolutionRowExtraDegeneracy_s' (X : SSet.{u}) (m : ℕ) :
    (edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s' =
      X.map (edgewiseBoundarySection m).op :=
  rfl

/-- The fixed-row extra degeneracy repeats the first right-block vertex. -/
@[simp]
theorem edgewiseResolutionRowExtraDegeneracy_s
    (X : SSet.{u}) (m n : ℕ) :
    (edgewiseResolutionRowExtraDegeneracy X (op ⦋m⦌)).s n =
      X.map (edgewiseBoundaryDegeneracy n m).op :=
  rfl

/-- The row carrier is exactly the fixed-inner row of the reversed
bisimplicial resolution. -/
theorem edgewiseResolutionRow_left (X : SSet.{u})
    (q : SimplexCategoryᵒᵖ) :
    (edgewiseResolutionRow X q).left =
      ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).obj
        (edgewiseResolution X).left).obj q :=
  rfl

/-- The row augmentation is exactly the corresponding transposed component
of the bisimplicial augmentation. -/
theorem edgewiseResolutionRow_hom (X : SSet.{u})
    (q : SimplexCategoryᵒᵖ) :
    (edgewiseResolutionRow X q).hom =
      ((CategoryTheory.SimplicialObject.transposeFunctor (Type u)).map
        (edgewiseResolution X).hom).app q :=
  rfl

end SSet

end
