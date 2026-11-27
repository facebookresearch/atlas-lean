/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# The finite Joyal interval

The finite interval of Cisinski, Higher Categories and Homotopical Algebra
(July 30, 2026), Construction 3.3.1 and Definition 3.3.3, is built by freely
adjoining a left inverse triangle and then a separate right inverse triangle
to the forward edge of the standard one-simplex.

Each step is one outer-horn pushout. The first horn fixes the forward edge and
the source identity; the second fixes the forward edge and the target identity.
The two missing edges are independent generators. The universal property
retains the full two-simplices, not just their relations in a homotopy category.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet

namespace joyalInterval

/-- The constant edge at the source of the standard forward edge. -/
def constSource : (Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  stdSimplex.σ (0 : Fin 1) ≫ stdSimplex.δ (1 : Fin 2)

/-- The constant edge at the target of the standard forward edge. -/
def constTarget : (Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  stdSimplex.σ (0 : Fin 1) ≫ stdSimplex.δ (0 : Fin 2)

@[reassoc (attr := simp)]
lemma δ_one_constSource :
    stdSimplex.δ (1 : Fin 2) ≫ constSource.{u} = stdSimplex.δ (1 : Fin 2) := by
  dsimp [constSource]
  rw [← Category.assoc]
  rw [show stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.σ (0 : Fin 1) =
      𝟙 (Δ[0] : SSet.{u}) by
    simpa using CosimplicialObject.δ_comp_σ_succ stdSimplex.{u} (i := (0 : Fin 1))]
  simp only [Category.id_comp]

@[reassoc (attr := simp)]
lemma δ_zero_constTarget :
    stdSimplex.δ (0 : Fin 2) ≫ constTarget.{u} = stdSimplex.δ (0 : Fin 2) := by
  dsimp [constTarget]
  rw [← Category.assoc]
  rw [show stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.σ (0 : Fin 1) =
      𝟙 (Δ[0] : SSet.{u}) by
    simpa using CosimplicialObject.δ_comp_σ_self stdSimplex.{u} (i := (0 : Fin 1))]
  simp only [Category.id_comp]

/-- Glue the forward (0,1) edge and the constant (0,2) edge. -/
noncomputable def leftAttach : (Λ[2, 0] : SSet.{u}) ⟶ Δ[1] :=
  horn₂₀.isPushout.desc (𝟙 _) constSource.{u} (by simp)

@[reassoc (attr := simp)]
lemma leftAttach_01 : horn₂₀.ι₀₁ ≫ leftAttach.{u} = 𝟙 (Δ[1] : SSet.{u}) :=
  horn₂₀.isPushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma leftAttach_02 : horn₂₀.ι₀₂ ≫ leftAttach.{u} = constSource.{u} :=
  horn₂₀.isPushout.inr_desc _ _ _

/-- Adjoin the left inverse and its complete unit triangle. -/
noncomputable def leftObj : SSet.{u} :=
  pushout leftAttach.{u} Λ[2, 0].ι

noncomputable def forwardLeft : (Δ[1] : SSet.{u}) ⟶ leftObj.{u} :=
  pushout.inl leftAttach.{u} Λ[2, 0].ι

noncomputable def triangleLeft : (Δ[2] : SSet.{u}) ⟶ leftObj.{u} :=
  pushout.inr leftAttach.{u} Λ[2, 0].ι

@[reassoc (attr := simp)]
lemma δ_two_triangleLeft :
    stdSimplex.δ (2 : Fin 3) ≫ triangleLeft.{u} = forwardLeft.{u} := by
  have h := congrArg (fun k => horn₂₀.ι₀₁ ≫ k)
    (pushout.condition (f := leftAttach.{u}) (g := Λ[2, 0].ι))
  simpa only [leftObj, ← Category.assoc, forwardLeft, triangleLeft,
    leftAttach_01, Category.id_comp, horn₂₀.ι₀₁, horn.ι_ι] using h.symm

@[reassoc (attr := simp)]
lemma δ_one_triangleLeft :
    stdSimplex.δ (1 : Fin 3) ≫ triangleLeft.{u} = constSource.{u} ≫ forwardLeft.{u} := by
  have h := congrArg (fun k => horn₂₀.ι₀₂ ≫ k)
    (pushout.condition (f := leftAttach.{u}) (g := Λ[2, 0].ι))
  simpa only [leftObj, ← Category.assoc, forwardLeft, triangleLeft,
    leftAttach_02, horn₂₀.ι₀₂, horn.ι_ι] using h.symm

/-- Glue the target identity (0,2) and the existing forward edge (1,2). -/
noncomputable def rightAttach : (Λ[2, 2] : SSet.{u}) ⟶ leftObj.{u} :=
  horn₂₂.isPushout.desc (constTarget.{u} ≫ forwardLeft.{u}) forwardLeft.{u} (by simp)

@[reassoc (attr := simp)]
lemma rightAttach_02 : horn₂₂.ι₀₂ ≫ rightAttach.{u} = constTarget.{u} ≫ forwardLeft.{u} :=
  horn₂₂.isPushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma rightAttach_12 : horn₂₂.ι₁₂ ≫ rightAttach.{u} = forwardLeft.{u} :=
  horn₂₂.isPushout.inr_desc _ _ _

end joyalInterval

/-- The finite Joyal interval, with separate left and right inverse triangles. -/
noncomputable def joyalInterval : SSet.{u} :=
  pushout joyalInterval.rightAttach.{u} Λ[2, 2].ι

namespace joyalInterval

/-- The standard forward edge of the finite interval. -/
noncomputable def forward : (Δ[1] : SSet.{u}) ⟶ joyalInterval.{u} :=
  forwardLeft.{u} ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι

/-- The full left inverse unit triangle. -/
noncomputable def leftTriangle : (Δ[2] : SSet.{u}) ⟶ joyalInterval.{u} :=
  triangleLeft.{u} ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι

/-- The full right inverse unit triangle. -/
noncomputable def rightTriangle : (Δ[2] : SSet.{u}) ⟶ joyalInterval.{u} :=
  pushout.inr rightAttach.{u} Λ[2, 2].ι

/-- The left inverse generator, adjoined by the first pushout. -/
noncomputable def leftInverse : (Δ[1] : SSet.{u}) ⟶ joyalInterval.{u} :=
  stdSimplex.δ (0 : Fin 3) ≫ leftTriangle.{u}

/-- The separate right inverse generator, adjoined by the second pushout. -/
noncomputable def rightInverse : (Δ[1] : SSet.{u}) ⟶ joyalInterval.{u} :=
  stdSimplex.δ (2 : Fin 3) ≫ rightTriangle.{u}

@[reassoc (attr := simp)]
lemma δ_zero_leftTriangle :
    stdSimplex.δ (0 : Fin 3) ≫ leftTriangle.{u} = leftInverse.{u} := rfl

@[reassoc (attr := simp)]
lemma δ_one_leftTriangle :
    stdSimplex.δ (1 : Fin 3) ≫ leftTriangle.{u} = constSource.{u} ≫ forward.{u} := by
  simpa only [joyalInterval, leftObj, leftTriangle, forward, Category.assoc] using
    congrArg (fun k => k ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι)
      δ_one_triangleLeft.{u}

@[reassoc (attr := simp)]
lemma δ_two_leftTriangle :
    stdSimplex.δ (2 : Fin 3) ≫ leftTriangle.{u} = forward.{u} := by
  simpa only [joyalInterval, leftObj, leftTriangle, forward, Category.assoc] using
    congrArg (fun k => k ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι)
      δ_two_triangleLeft.{u}

@[reassoc (attr := simp)]
lemma δ_zero_rightTriangle :
    stdSimplex.δ (0 : Fin 3) ≫ rightTriangle.{u} = forward.{u} := by
  have h := congrArg (fun k => horn₂₂.ι₁₂ ≫ k)
    (pushout.condition (f := rightAttach.{u}) (g := Λ[2, 2].ι))
  have h₁ :
      stdSimplex.δ (0 : Fin 3) ≫ rightTriangle.{u} =
        (horn₂₂.ι₁₂ ≫ rightAttach.{u}) ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι := by
    simpa only [joyalInterval, leftObj, ← Category.assoc, rightTriangle,
      horn₂₂.ι₁₂, horn.ι_ι] using h.symm
  exact h₁.trans (congrArg
    (fun k => k ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι) rightAttach_12.{u})

@[reassoc (attr := simp)]
lemma δ_one_rightTriangle :
    stdSimplex.δ (1 : Fin 3) ≫ rightTriangle.{u} = constTarget.{u} ≫ forward.{u} := by
  have h := congrArg (fun k => horn₂₂.ι₀₂ ≫ k)
    (pushout.condition (f := rightAttach.{u}) (g := Λ[2, 2].ι))
  have h₁ :
      stdSimplex.δ (1 : Fin 3) ≫ rightTriangle.{u} =
        (horn₂₂.ι₀₂ ≫ rightAttach.{u}) ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι := by
    simpa only [joyalInterval, leftObj, ← Category.assoc, rightTriangle,
      horn₂₂.ι₀₂, horn.ι_ι] using h.symm
  exact h₁.trans ((congrArg
    (fun k => k ≫ pushout.inl rightAttach.{u} Λ[2, 2].ι) rightAttach_02.{u}).trans
      (Category.assoc constTarget.{u} forwardLeft.{u}
        (pushout.inl rightAttach.{u} Λ[2, 2].ι)))

@[reassoc (attr := simp)]
lemma δ_two_rightTriangle :
    stdSimplex.δ (2 : Fin 3) ≫ rightTriangle.{u} = rightInverse.{u} := rfl

section UniversalProperty

variable {X : SSet.{u}} (f : Δ[1] ⟶ X) (L R : Δ[2] ⟶ X)
  (hL₂ : stdSimplex.δ (2 : Fin 3) ≫ L = f)
  (hL₁ : stdSimplex.δ (1 : Fin 3) ≫ L = constSource.{u} ≫ f)
  (hR₀ : stdSimplex.δ (0 : Fin 3) ≫ R = f)
  (hR₁ : stdSimplex.δ (1 : Fin 3) ≫ R = constTarget.{u} ≫ f)

/-- Realize the forward edge and left triangle at the first stage. -/
noncomputable def descLeft : leftObj.{u} ⟶ X :=
  pushout.desc f L (by
    apply horn₂₀.isPushout.hom_ext
    · simpa only [← Category.assoc, leftAttach_01, Category.id_comp,
        horn₂₀.ι₀₁, horn.ι_ι] using hL₂.symm
    · simpa only [← Category.assoc, leftAttach_02,
        horn₂₀.ι₀₂, horn.ι_ι] using hL₁.symm)

@[reassoc (attr := simp)]
lemma forwardLeft_descLeft : forwardLeft.{u} ≫ descLeft f L hL₂ hL₁ = f :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma triangleLeft_descLeft : triangleLeft.{u} ≫ descLeft f L hL₂ hL₁ = L :=
  pushout.inr_desc _ _ _

/-- Realize both complete triangles, with independent missing edges. -/
noncomputable def desc : joyalInterval.{u} ⟶ X :=
  pushout.desc (descLeft f L hL₂ hL₁) R (by
    apply horn₂₂.isPushout.hom_ext
    · simp only [← Category.assoc]
      rw [rightAttach_02, Category.assoc, forwardLeft_descLeft,
        horn₂₂.ι₀₂, horn.ι_ι]
      exact hR₁.symm
    · simp only [← Category.assoc]
      rw [rightAttach_12, forwardLeft_descLeft, horn₂₂.ι₁₂, horn.ι_ι]
      exact hR₀.symm)

@[reassoc (attr := simp)]
lemma forward_desc : forward.{u} ≫ desc f L R hL₂ hL₁ hR₀ hR₁ = f := by
  simp only [joyalInterval, leftObj, forward, Category.assoc, desc, pushout.inl_desc]
  exact forwardLeft_descLeft f L hL₂ hL₁

@[reassoc (attr := simp)]
lemma leftTriangle_desc : leftTriangle.{u} ≫ desc f L R hL₂ hL₁ hR₀ hR₁ = L := by
  simp only [joyalInterval, leftObj, leftTriangle, Category.assoc, desc, pushout.inl_desc]
  exact triangleLeft_descLeft f L hL₂ hL₁

@[reassoc (attr := simp)]
lemma rightTriangle_desc : rightTriangle.{u} ≫ desc f L R hL₂ hL₁ hR₀ hR₁ = R :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
lemma leftInverse_desc :
    leftInverse.{u} ≫ desc f L R hL₂ hL₁ hR₀ hR₁ = stdSimplex.δ (0 : Fin 3) ≫ L := by
  simp only [leftInverse, Category.assoc, leftTriangle_desc]

@[reassoc (attr := simp)]
lemma rightInverse_desc :
    rightInverse.{u} ≫ desc f L R hL₂ hL₁ hR₀ hR₁ = stdSimplex.δ (2 : Fin 3) ≫ R := by
  simp only [rightInverse, Category.assoc, rightTriangle_desc]

end UniversalProperty

/-- Maps out of the interval are determined by the forward edge and full triangles. -/
@[ext]
lemma hom_ext {X : SSet.{u}} {a b : joyalInterval.{u} ⟶ X}
    (hf : forward.{u} ≫ a = forward.{u} ≫ b)
    (hL : leftTriangle.{u} ≫ a = leftTriangle.{u} ≫ b)
    (hR : rightTriangle.{u} ≫ a = rightTriangle.{u} ≫ b) : a = b := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · simpa only [joyalInterval, leftObj, forward, forwardLeft, Category.assoc] using hf
    · simpa only [joyalInterval, leftObj, leftTriangle, triangleLeft, Category.assoc] using hL
  · exact hR

/-- Every compatible pair of full inverse triangles has a unique realization. -/
theorem existsUnique_desc {X : SSet.{u}} (f : Δ[1] ⟶ X) (L R : Δ[2] ⟶ X)
    (hL₂ : stdSimplex.δ (2 : Fin 3) ≫ L = f)
    (hL₁ : stdSimplex.δ (1 : Fin 3) ≫ L = constSource.{u} ≫ f)
    (hR₀ : stdSimplex.δ (0 : Fin 3) ≫ R = f)
    (hR₁ : stdSimplex.δ (1 : Fin 3) ≫ R = constTarget.{u} ≫ f) :
    ∃! a : joyalInterval.{u} ⟶ X,
      forward.{u} ≫ a = f ∧ leftTriangle.{u} ≫ a = L ∧ rightTriangle.{u} ≫ a = R := by
  refine ⟨desc f L R hL₂ hL₁ hR₀ hR₁,
    ⟨forward_desc .., leftTriangle_desc .., rightTriangle_desc ..⟩, ?_⟩
  intro a ha
  exact hom_ext
    (ha.1.trans (forward_desc ..).symm)
    (ha.2.1.trans (leftTriangle_desc ..).symm)
    (ha.2.2.trans (rightTriangle_desc ..).symm)

/-- The full presentation property, retaining both independent inverse edges. -/
theorem existsUnique_realization {X : SSet.{u}}
    (f g h : Δ[1] ⟶ X) (L R : Δ[2] ⟶ X)
    (hL₀ : stdSimplex.δ (0 : Fin 3) ≫ L = g)
    (hL₁ : stdSimplex.δ (1 : Fin 3) ≫ L = constSource.{u} ≫ f)
    (hL₂ : stdSimplex.δ (2 : Fin 3) ≫ L = f)
    (hR₀ : stdSimplex.δ (0 : Fin 3) ≫ R = f)
    (hR₁ : stdSimplex.δ (1 : Fin 3) ≫ R = constTarget.{u} ≫ f)
    (hR₂ : stdSimplex.δ (2 : Fin 3) ≫ R = h) :
    ∃! a : joyalInterval.{u} ⟶ X,
      forward.{u} ≫ a = f ∧
      leftInverse.{u} ≫ a = g ∧
      rightInverse.{u} ≫ a = h ∧
      leftTriangle.{u} ≫ a = L ∧ rightTriangle.{u} ≫ a = R := by
  refine ⟨desc f L R hL₂ hL₁ hR₀ hR₁,
    ⟨forward_desc .., (leftInverse_desc ..).trans hL₀,
      (rightInverse_desc ..).trans hR₂, leftTriangle_desc .., rightTriangle_desc ..⟩, ?_⟩
  intro a ha
  exact hom_ext
    (ha.1.trans (forward_desc ..).symm)
    (ha.2.2.2.1.trans (leftTriangle_desc ..).symm)
    (ha.2.2.2.2.trans (rightTriangle_desc ..).symm)

/-- The source (index 0) and target (index 1) endpoints of the finite interval. -/
noncomputable def endpoint (ε : Fin 2) : (Δ[0] : SSet.{u}) ⟶ joyalInterval.{u} :=
  stdSimplex.δ ε.rev ≫ forward.{u}

@[reassoc (attr := simp)]
lemma endpoint_zero :
    endpoint.{u} (0 : Fin 2) = stdSimplex.δ (1 : Fin 2) ≫ forward.{u} := rfl

@[reassoc (attr := simp)]
lemma endpoint_one :
    endpoint.{u} (1 : Fin 2) = stdSimplex.δ (0 : Fin 2) ≫ forward.{u} := rfl

end joyalInterval

end SSet
