/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Topology.ContinuousBorel

/-!
# Actual group-change and fibre maps in the continuous Borel model

Group change applies the original continuous homomorphism to every
coordinate of the homogeneous bar construction. The fibre is the
realization of the singular set of the original space, mapped using
the identity group coordinate in every simplicial degree.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.Topology.ContinuousBorelGroupMaps

open _root_.CategoryTheory _root_.Opposite
open ContinuousBorel

variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  {Z W : TopCat.{0}} [MulAction G Z] [MulAction H W]
  [ContinuousSMul G Z] [ContinuousSMul H W]

/-- The actual map on every homogeneous orbit quotient. -/
def levelHom (φ : G →* H) (f : Z ⟶ W)
    (hf : ∀ (g : G) (x : Z), f (g • x) = φ g • f x) (n : ℕ) :
    BarLevel G Z n → BarLevel H W n :=
  Quotient.map (fun p => (φ ∘ p.1, f p.2)) (by
    intro a b h
    change a ∈ MulAction.orbit G b at h
    change _ ∈ MulAction.orbit H _
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨φ g, Prod.ext ?_ (hf g b.2).symm⟩
    funext i
    exact (φ.map_mul g (b.1 i)).symm)

/-- All simplicial maps retain the original continuous group homomorphism. -/
def barHom (φ : G →* H) (hφ : Continuous φ) (f : Z ⟶ W)
    (hf : ∀ (g : G) (x : Z), f (g • x) = φ g • f x) : bar G Z ⟶ bar H W where
  app n := TopCat.ofHom ⟨levelHom φ f hf n.unop.len,
    continuous_coinduced_dom.2 (continuous_quot_mk.comp
      ((continuous_pi (fun i => hφ.comp ((continuous_apply i).comp continuous_fst))).prodMk
        (f.hom.continuous.comp continuous_snd)))⟩
  naturality i j a := by ext p; induction p using Quotient.inductionOn; rfl

/-- Group change on the existing native singular-realization homotopy quotient. -/
def borelHom (φ : G →* H) (hφ : Continuous φ) (f : Z ⟶ W)
    (hf : ∀ (g : G) (x : Z), f (g • x) = φ g • f x) : borel G Z ⟶ borel H W :=
  SSet.toTop.map
    (diagonalFunctor.map (Functor.whiskerRight (barHom φ hφ f hf) TopCat.toSSet))

variable (G Z)

/-- Every group coordinate in the fibre map is the actual identity. -/
def barFiber : (Functor.const SimplexCategoryᵒᵖ).obj Z ⟶ bar G Z where
  app n := TopCat.ofHom ⟨fun x => Quotient.mk'' ((fun _ : Fin (n.unop.len+1) => 1), x),
    continuous_quot_mk.comp (continuous_const.prodMk continuous_id)⟩
  naturality i j f := by ext x; rfl

/-- The actual singular-set map into the diagonal bar construction. -/
def singularFiber : TopCat.toSSet.obj Z ⟶ diagonalSingular G Z :=
  (diagonalConstIso (TopCat.toSSet.obj Z)).inv ≫
    diagonalFunctor.map (Functor.constComp SimplexCategoryᵒᵖ Z TopCat.toSSet).inv ≫
      diagonalFunctor.map (Functor.whiskerRight (barFiber G Z) TopCat.toSSet)

/-- The Borel fibre map is native geometric realization of that same map. -/
def realizedFiber : SSet.toTop.obj (TopCat.toSSet.obj Z) ⟶ borel G Z :=
  SSet.toTop.map (singularFiber G Z)

end MathlibExt.Topology.ContinuousBorelGroupMaps
