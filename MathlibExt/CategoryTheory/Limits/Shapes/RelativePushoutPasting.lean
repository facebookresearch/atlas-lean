/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

section

-- Author: @toskua, Codex


/-!
# Relative source enlargement for a morphism of actual pushout squares

The two supplied pushout squares are source geometry. Their original comparison triangles
give a pushout square whose left map is the actual lower relative corner and whose right
map enlarges the relative source. No class preservation or relative-corner outcome is an
input to the construction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Limits.RelativePushoutPasting

variable (C : Type u) [Category.{v} C]

/-- Two actual pushout squares, their original morphism, and an actual source cocone. -/
structure Data where
  /-- The common source of the span in the original pushout square. -/
  I : C
  /-- The target of `v` and source of `j` in the original pushout square. -/
  J : C
  /-- The target of `u` and source of `k` in the original pushout square. -/
  V : C
  /-- The pushout vertex of the original square, with its cocone map `g` to `X`. -/
  K : C
  /-- The common source of the span in the enlarged pushout square. -/
  I' : C
  /-- The target of `v'` and source of `j'` in the enlarged pushout square. -/
  J' : C
  /-- The target of `u'` and source of `k'` in the enlarged pushout square. -/
  V' : C
  /-- The pushout vertex of the enlarged square. -/
  K' : C
  /-- The target of the original cocone maps `a`, `b`, and `g`. -/
  X : C
  /-- The span leg from `I` to `J` in the original pushout square. -/
  v : I ⟶ J
  /-- The span leg from `I` to `V` in the original pushout square. -/
  u : I ⟶ V
  /-- The cocone leg from `J` to `K` in the original pushout square. -/
  j : J ⟶ K
  /-- The cocone leg from `V` to `K` in the original pushout square. -/
  k : V ⟶ K
  square : IsPushout v u j k
  /-- The span leg from `I'` to `J'` in the enlarged pushout square. -/
  v' : I' ⟶ J'
  /-- The span leg from `I'` to `V'` in the enlarged pushout square. -/
  u' : I' ⟶ V'
  /-- The cocone leg from `J'` to `K'` in the enlarged pushout square. -/
  j' : J' ⟶ K'
  /-- The cocone leg from `V'` to `K'` in the enlarged pushout square. -/
  k' : V' ⟶ K'
  square' : IsPushout v' u' j' k'
  /-- The source component `I ⟶ I'` of the morphism between the pushout squares. -/
  iI : I ⟶ I'
  /-- The component `J ⟶ J'` comparing the targets of the two `v` span legs. -/
  iJ : J ⟶ J'
  /-- The component `V ⟶ V'` comparing the targets of the two `u` span legs. -/
  iV : V ⟶ V'
  /-- The component `K ⟶ K'` comparing the two pushout vertices. -/
  iK : K ⟶ K'
  v_iJ : v ≫ iJ = iI ≫ v'
  u_iV : u ≫ iV = iI ≫ u'
  j_iK : j ≫ iK = iJ ≫ j'
  k_iK : k ≫ iK = iV ≫ k'
  /-- The cocone leg from `J` to `X`, agreeing with `j ≫ g`. -/
  a : J ⟶ X
  /-- The cocone leg from `V` to `X`, agreeing with `k ≫ g`. -/
  b : V ⟶ X
  /-- The map from the original pushout vertex `K` to the cocone vertex `X`. -/
  g : K ⟶ X
  j_g : j ≫ g = a
  k_g : k ≫ g = b

namespace Data

variable {C} [HasPushouts C] (D : Data C)

/-- The relative source before attaching the new piece. -/
abbrev smallSource : C := pushout D.a D.iJ

/-- The relative source after attaching the new piece. -/
abbrev largeSource : C := pushout D.g D.iK

/-- The unchanged lower relative source. -/
abbrev lowerSource : C := pushout D.u D.iI

/-- The actual lower relative corner, retaining both supplied source legs. -/
def lowerCorner : D.lowerSource ⟶ D.V' :=
  pushout.desc D.iV D.u' D.u_iV

@[reassoc (attr := simp)]
theorem lowerCorner_inl : pushout.inl D.u D.iI ≫ D.lowerCorner = D.iV :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem lowerCorner_inr : pushout.inr D.u D.iI ≫ D.lowerCorner = D.u' :=
  pushout.inr_desc _ _ _

theorem toSmall_condition :
    D.u ≫ (D.b ≫ pushout.inl D.a D.iJ) = D.iI ≫ (D.v' ≫ pushout.inr D.a D.iJ) := by
  calc
    D.u ≫ (D.b ≫ pushout.inl D.a D.iJ) = (D.u ≫ D.k) ≫ D.g ≫ pushout.inl D.a D.iJ := by
      simpa only [Category.assoc] using
        congrArg (fun f => D.u ≫ f ≫ pushout.inl D.a D.iJ) D.k_g.symm
    _ = (D.v ≫ D.j) ≫ D.g ≫ pushout.inl D.a D.iJ := by rw [D.square.w]
    _ = D.v ≫ D.a ≫ pushout.inl D.a D.iJ := by
      simpa only [Category.assoc] using
        congrArg (fun f => D.v ≫ f ≫ pushout.inl D.a D.iJ) D.j_g
    _ = D.v ≫ D.iJ ≫ pushout.inr D.a D.iJ := by rw [pushout.condition]
    _ = D.iI ≫ (D.v' ≫ pushout.inr D.a D.iJ) := by rw [← Category.assoc, D.v_iJ, Category.assoc]

/-- The original comparison from the lower relative source to the old relative source. -/
def toSmall : D.lowerSource ⟶ D.smallSource :=
  pushout.desc (D.b ≫ pushout.inl D.a D.iJ) (D.v' ≫ pushout.inr D.a D.iJ) D.toSmall_condition

@[reassoc (attr := simp)]
theorem toSmall_inl : pushout.inl D.u D.iI ≫ D.toSmall = D.b ≫ pushout.inl D.a D.iJ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem toSmall_inr : pushout.inr D.u D.iI ≫ D.toSmall = D.v' ≫ pushout.inr D.a D.iJ :=
  pushout.inr_desc _ _ _

theorem toLarge_condition :
    D.a ≫ pushout.inl D.g D.iK = D.iJ ≫ (D.j' ≫ pushout.inr D.g D.iK) := by
  calc
    D.a ≫ pushout.inl D.g D.iK = D.j ≫ (D.g ≫ pushout.inl D.g D.iK) := by
      rw [← Category.assoc, D.j_g]
    _ = D.j ≫ (D.iK ≫ pushout.inr D.g D.iK) := by rw [pushout.condition]
    _ = D.iJ ≫ (D.j' ≫ pushout.inr D.g D.iK) := by rw [← Category.assoc, D.j_iK, Category.assoc]

/-- The actual relative source enlargement, with the original coefficient unchanged. -/
def toLarge : D.smallSource ⟶ D.largeSource :=
  pushout.desc (pushout.inl D.g D.iK) (D.j' ≫ pushout.inr D.g D.iK) D.toLarge_condition

@[reassoc (attr := simp)]
theorem toLarge_inl : pushout.inl D.a D.iJ ≫ D.toLarge = pushout.inl D.g D.iK :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem toLarge_inr : pushout.inr D.a D.iJ ≫ D.toLarge = D.j' ≫ pushout.inr D.g D.iK :=
  pushout.inr_desc _ _ _

/-- The original new-piece map into the enlarged relative source. -/
def lowerTarget : D.V' ⟶ D.largeSource := D.k' ≫ pushout.inr D.g D.iK

/-- The relative attachment square commutes on both original lower pushout legs. -/
theorem condition : D.toSmall ≫ D.toLarge = D.lowerCorner ≫ D.lowerTarget := by
  apply pushout.hom_ext
  · simp only [toSmall_inl_assoc, toLarge_inl, lowerCorner_inl_assoc, lowerTarget]
    calc
      D.b ≫ pushout.inl D.g D.iK = D.k ≫ (D.g ≫ pushout.inl D.g D.iK) := by
        rw [← Category.assoc, D.k_g]
      _ = D.k ≫ (D.iK ≫ pushout.inr D.g D.iK) := by rw [pushout.condition]
      _ = D.iV ≫ (D.k' ≫ pushout.inr D.g D.iK) := by
        rw [← Category.assoc, D.k_iK, Category.assoc]
  · simp only [toSmall_inr_assoc, toLarge_inr, lowerCorner_inr_assoc, lowerTarget]
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ pushout.inr D.g D.iK) D.square'.w

/-- The original relative legs jointly determine every map out of the enlarged source. -/
theorem hom_ext {Z : C} {r s : D.largeSource ⟶ Z}
    (h₁ : D.toLarge ≫ r = D.toLarge ≫ s)
    (h₂ : D.lowerTarget ≫ r = D.lowerTarget ≫ s) : r = s := by
  apply pushout.hom_ext
  · have h := congrArg (fun f => pushout.inl D.a D.iJ ≫ f) h₁
    simpa only [Category.assoc, toLarge_inl_assoc] using h
  · apply D.square'.hom_ext
    · have h := congrArg (fun f => pushout.inr D.a D.iJ ≫ f) h₁
      simpa only [Category.assoc, toLarge_inr_assoc] using h
    · simpa only [lowerTarget, Category.assoc] using h₂

/-- Every compatible pair on the two original relative legs descends to the enlarged source. -/
theorem exists_desc {Z : C} (r : D.smallSource ⟶ Z) (s : D.V' ⟶ Z)
    (w : D.toSmall ≫ r = D.lowerCorner ≫ s) :
    ∃ l : D.largeSource ⟶ Z, D.toLarge ≫ l = r ∧ D.lowerTarget ≫ l = s := by
  have wI : D.v' ≫ (pushout.inr D.a D.iJ ≫ r) = D.u' ≫ s := by
    have h := congrArg (fun f => pushout.inr D.u D.iI ≫ f) w
    simpa only [Category.assoc, toSmall_inr_assoc, lowerCorner_inr_assoc] using h
  let t := D.square'.desc (pushout.inr D.a D.iJ ≫ r) s wI
  have wtJ : D.j' ≫ t = pushout.inr D.a D.iJ ≫ r := D.square'.inl_desc _ _ _
  have wtV : D.k' ≫ t = s := D.square'.inr_desc _ _ _
  have wV : D.b ≫ (pushout.inl D.a D.iJ ≫ r) = D.iV ≫ s := by
    have h := congrArg (fun f => pushout.inl D.u D.iI ≫ f) w
    simpa only [Category.assoc, toSmall_inl_assoc, lowerCorner_inl_assoc] using h
  have wt : D.g ≫ (pushout.inl D.a D.iJ ≫ r) = D.iK ≫ t := by
    apply D.square.hom_ext
    · calc
        D.j ≫ (D.g ≫ (pushout.inl D.a D.iJ ≫ r)) =
            D.a ≫ pushout.inl D.a D.iJ ≫ r := by rw [← Category.assoc, D.j_g]
        _ = D.iJ ≫ pushout.inr D.a D.iJ ≫ r := by
          simpa only [Category.assoc] using
            congrArg (fun f => f ≫ r) (pushout.condition (f := D.a) (g := D.iJ))
        _ = D.iJ ≫ (D.j' ≫ t) := by rw [wtJ]
        _ = D.j ≫ (D.iK ≫ t) := by rw [← Category.assoc, ← D.j_iK, Category.assoc]
    · calc
        D.k ≫ (D.g ≫ (pushout.inl D.a D.iJ ≫ r)) =
            D.b ≫ (pushout.inl D.a D.iJ ≫ r) := by rw [← Category.assoc, D.k_g]
        _ = D.iV ≫ s := wV
        _ = D.iV ≫ (D.k' ≫ t) := by rw [wtV]
        _ = D.k ≫ (D.iK ≫ t) := by rw [← Category.assoc, ← D.k_iK, Category.assoc]
  refine ⟨pushout.desc (pushout.inl D.a D.iJ ≫ r) t wt, ?_, ?_⟩
  · apply pushout.hom_ext
    · simp only [toLarge_inl_assoc, pushout.inl_desc]
    · simp only [toLarge_inr_assoc, pushout.inr_desc]
      exact wtJ
  · dsimp only [lowerTarget]
    simp only [Category.assoc, pushout.inr_desc]
    exact wtV

/-- The relative source enlargement is an actual cobase change of the lower corner. -/
theorem isPushout : IsPushout D.toSmall D.lowerCorner D.toLarge D.lowerTarget :=
  IsPushout.mk' D.condition (fun _ _ _ h₁ h₂ => D.hom_ext h₁ h₂)
    (fun _ r s w => D.exists_desc r s w)

/-- Only ordinary cobase-change closure is needed for the actual relative source enlargement. -/
theorem toLarge_mem (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    (h : P D.lowerCorner) : P D.toLarge :=
  P.of_isPushout D.isPushout h

end Data

end CategoryTheory.Limits.RelativePushoutPasting

end
end
end

section

-- Author: @toskua, Codex


/-!
# Original relative-corner readbacks for pushout attachment

The actual old relative corner is the actual source enlargement followed by the actual
enlarged corner. Both original source legs are retained. This is the composition identity
used by finite partial-boundary induction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace CategoryTheory.Limits.RelativePushoutPasting.Data

variable {C : Type u} [Category.{v} C] [HasPushouts C] (D : RelativePushoutPasting.Data C)
variable {X' : C} (iX : D.X ⟶ X') (g' : D.K' ⟶ X')

omit [HasPushouts C] in
/-- The old corner retains the original comparison triangle through the enlarged cocone. -/
theorem oldCornerCondition (w : D.g ≫ iX = D.iK ≫ g') : D.a ≫ iX = D.iJ ≫ (D.j' ≫ g') := by
  calc
    D.a ≫ iX = D.j ≫ (D.g ≫ iX) := by rw [← Category.assoc, D.j_g]
    _ = D.j ≫ (D.iK ≫ g') := by rw [w]
    _ = D.iJ ≫ (D.j' ≫ g') := by rw [← Category.assoc, D.j_iK, Category.assoc]

variable (w : D.g ≫ iX = D.iK ≫ g')

/-- The enlarged original relative corner. -/
def enlargedCorner : D.largeSource ⟶ X' := pushout.desc iX g' w

/-- The old original relative corner with its target cocone comparison retained. -/
def oldCorner : D.smallSource ⟶ X' :=
  pushout.desc iX (D.j' ≫ g') (D.oldCornerCondition iX g' w)

@[reassoc (attr := simp)]
theorem enlargedCorner_inl : pushout.inl D.g D.iK ≫ D.enlargedCorner iX g' w = iX :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem enlargedCorner_inr : pushout.inr D.g D.iK ≫ D.enlargedCorner iX g' w = g' :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem oldCorner_inl : pushout.inl D.a D.iJ ≫ D.oldCorner iX g' w = iX :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem oldCorner_inr : pushout.inr D.a D.iJ ≫ D.oldCorner iX g' w = D.j' ≫ g' :=
  pushout.inr_desc _ _ _

/-- The actual old corner is the source enlargement followed by the actual enlarged corner. -/
theorem toLarge_enlargedCorner :
    D.toLarge ≫ D.enlargedCorner iX g' w = D.oldCorner iX g' w := by
  apply pushout.hom_ext
  · simp only [toLarge_inl_assoc, enlargedCorner_inl, oldCorner_inl]
  · simp only [toLarge_inr_assoc, enlargedCorner_inr, oldCorner_inr]

end CategoryTheory.Limits.RelativePushoutPasting.Data

end
end
end
