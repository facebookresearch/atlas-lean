/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.RealizedBasedWhitehead
import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularHomotopyRelAtPoint
import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyRelAtVertex

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

#check TopCat.realizedBasedHomotopyInverse
#print axioms TopCat.realizedBasedHomotopyInverse
#check TopCat.realizedBasedHomotopyInverse_point
#print axioms TopCat.realizedBasedHomotopyInverse_point
#check TopCat.realizedBasedLeftHomotopy
#print axioms TopCat.realizedBasedLeftHomotopy
#check TopCat.realizedBasedRightHomotopy
#print axioms TopCat.realizedBasedRightHomotopy
#check TopCat.realizedBasedHomotopyEquiv
#print axioms TopCat.realizedBasedHomotopyEquiv
#check TopCat.realizedBasedHomotopyEquiv_toFun
#print axioms TopCat.realizedBasedHomotopyEquiv_toFun
#check TopCat.realizedBasedHomotopyEquiv_invFun
#print axioms TopCat.realizedBasedHomotopyEquiv_invFun
#check TopCat.singularHomotopyRelAtPoint
#print axioms TopCat.singularHomotopyRelAtPoint
#check TopCat.singularHomotopyRelAtPoint_h
#print axioms TopCat.singularHomotopyRelAtPoint_h

section ActualRealizedMap

variable {K L : SSet.{u}} (x : K _⦋0⦌) (y : L _⦋0⦌)
  (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
  (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
  (hf : TopCat.weakHomotopyEquivalences f)

example :
    (TopCat.realizedBasedHomotopyEquiv x y f hxy hf).toFun = f.hom ∧
      (TopCat.realizedBasedHomotopyEquiv x y f hxy hf).invFun =
        (TopCat.realizedBasedHomotopyInverse x y f hxy hf).hom :=
  ⟨TopCat.realizedBasedHomotopyEquiv_toFun x y f hxy hf,
    TopCat.realizedBasedHomotopyEquiv_invFun x y f hxy hf⟩

example :
    TopCat.realizedBasedHomotopyInverse x y f hxy hf (SSet.realizedVertex y) =
      SSet.realizedVertex x :=
  TopCat.realizedBasedHomotopyInverse_point x y f hxy hf

example (t : unitInterval) :
    TopCat.realizedBasedLeftHomotopy x y f hxy hf (t, SSet.realizedVertex x) =
      SSet.realizedVertex x := by
  have h := (TopCat.realizedBasedLeftHomotopy x y f hxy hf).eq_fst t
    (Set.mem_singleton_iff.mpr rfl)
  calc
    _ = (f ≫ TopCat.realizedBasedHomotopyInverse x y f hxy hf)
        (SSet.realizedVertex x) := h
    _ = SSet.realizedVertex x := by
      change TopCat.realizedBasedHomotopyInverse x y f hxy hf
        (f (SSet.realizedVertex x)) = SSet.realizedVertex x
      rw [hxy, TopCat.realizedBasedHomotopyInverse_point]

example (t : unitInterval) :
    TopCat.realizedBasedRightHomotopy x y f hxy hf (t, SSet.realizedVertex y) =
      SSet.realizedVertex y := by
  have h := (TopCat.realizedBasedRightHomotopy x y f hxy hf).eq_fst t
    (Set.mem_singleton_iff.mpr rfl)
  calc
    _ = (TopCat.realizedBasedHomotopyInverse x y f hxy hf ≫ f)
        (SSet.realizedVertex y) := h
    _ = SSet.realizedVertex y := by
      change f (TopCat.realizedBasedHomotopyInverse x y f hxy hf
        (SSet.realizedVertex y)) = SSet.realizedVertex y
      rw [TopCat.realizedBasedHomotopyInverse_point]
      exact hxy

example :
    (TopCat.realizedBasedLeftHomotopy x y f hxy hf).toHomotopy.curry 0 =
        (f ≫ TopCat.realizedBasedHomotopyInverse x y f hxy hf).hom ∧
      (TopCat.realizedBasedLeftHomotopy x y f hxy hf).toHomotopy.curry 1 =
        (𝟙 (SSet.toTop.obj K) : SSet.toTop.obj K ⟶ SSet.toTop.obj K).hom :=
  ⟨(TopCat.realizedBasedLeftHomotopy x y f hxy hf).toHomotopy.curry_zero,
    (TopCat.realizedBasedLeftHomotopy x y f hxy hf).toHomotopy.curry_one⟩

example :
    (TopCat.realizedBasedRightHomotopy x y f hxy hf).toHomotopy.curry 0 =
        (TopCat.realizedBasedHomotopyInverse x y f hxy hf ≫ f).hom ∧
      (TopCat.realizedBasedRightHomotopy x y f hxy hf).toHomotopy.curry 1 =
        (𝟙 (SSet.toTop.obj L) : SSet.toTop.obj L ⟶ SSet.toTop.obj L).hom :=
  ⟨(TopCat.realizedBasedRightHomotopy x y f hxy hf).toHomotopy.curry_zero,
    (TopCat.realizedBasedRightHomotopy x y f hxy hf).toHomotopy.curry_one⟩

end ActualRealizedMap

-- Both sides of the actual counit at a realization are original realizations.
-- Its weakness and literal point equation are derived from existing providers.
example (K : SSet.{u}) (x : K _⦋0⦌) :
    let D : TopCat.{u} := SSet.toTop.obj K
    let sx : (TopCat.toSSet.obj D) _⦋0⦌ :=
      TopCat.toSSetObj₀Equiv.symm (SSet.realizedVertex x)
    let ε : SSet.toTop.obj (TopCat.toSSet.obj D) ⟶ D := sSetTopAdj.counit.app D
    ∃ g : D ⟶ SSet.toTop.obj (TopCat.toSSet.obj D),
      g (SSet.realizedVertex x) = SSet.realizedVertex sx ∧
      Nonempty (ContinuousMap.HomotopyRel (ε ≫ g).hom
        (𝟙 (SSet.toTop.obj (TopCat.toSSet.obj D)) :
          SSet.toTop.obj (TopCat.toSSet.obj D) ⟶
          SSet.toTop.obj (TopCat.toSSet.obj D)).hom
        {SSet.realizedVertex sx}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ ε).hom
        (𝟙 D : D ⟶ D).hom {SSet.realizedVertex x}) := by
  dsimp only
  let D : TopCat.{u} := SSet.toTop.obj K
  let sx : (TopCat.toSSet.obj D) _⦋0⦌ :=
    TopCat.toSSetObj₀Equiv.symm (SSet.realizedVertex x)
  let ε : SSet.toTop.obj (TopCat.toSSet.obj D) ⟶ D := sSetTopAdj.counit.app D
  have hxy : ε (SSet.realizedVertex sx) = SSet.realizedVertex x := by
    simpa only [sx, Equiv.apply_symm_apply] using TopCat.counit_realizedVertex sx
  have hf : TopCat.weakHomotopyEquivalences ε :=
    SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences D
  exact ⟨TopCat.realizedBasedHomotopyInverse sx x ε hxy hf,
    TopCat.realizedBasedHomotopyInverse_point sx x ε hxy hf,
    ⟨TopCat.realizedBasedLeftHomotopy sx x ε hxy hf⟩,
    ⟨TopCat.realizedBasedRightHomotopy sx x ε hxy hf⟩⟩

section ActualStationarySingularHomotopy

variable {X Y : TopCat.{u}} {f g : X ⟶ Y}
  (x₀ : X) (H : ContinuousMap.HomotopyRel f.hom g.hom {x₀})

example :
    (TopCat.singularHomotopyRelAtPoint x₀ H).h =
      (TopCat.Homotopy.toSSet (H.toHomotopy : TopCat.Homotopy f g)).h :=
  TopCat.singularHomotopyRelAtPoint_h x₀ H

example (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n)
    (hσ : σ ∈ (SSet.Subcomplex.range
      (SSet.const (X := (Δ[0] : SSet.{u})) (TopCat.toSSetObj₀Equiv.symm x₀))).obj n)
    (t : (Δ[1] : SSet.{u}).obj n) :
    (TopCat.singularHomotopyRelAtPoint x₀ H).h.app n (σ, t) =
      (TopCat.toSSet.map f).app n σ :=
  (TopCat.singularHomotopyRelAtPoint x₀ H).stationary σ hσ t

-- This is the exact fixed-point consequence needed after singularizing the
-- actual relative domination homotopy and postcomposing with its actual counit.
example (t : unitInterval) :
    let sx : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x₀
    let S := SSet.Subcomplex.range (SSet.const (X := (Δ[0] : SSet.{u})) sx)
    ∃ hx : sx ∈ S.obj (op ⦋0⦌),
      sSetTopAdj.counit.app Y
          (SSet.realizeHomotopyRelAtVertex
            (TopCat.singularHomotopyRelAtPoint x₀ H) sx hx
            (t, SSet.realizedVertex sx)) = f x₀ := by
  dsimp only
  let sx : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x₀
  have hx : sx ∈ (SSet.Subcomplex.range (SSet.const (X := (Δ[0] : SSet.{u})) sx)).obj (op ⦋0⦌) := by
    change sx ∈ Set.range ((SSet.const (X := (Δ[0] : SSet.{u})) sx : (Δ[0] : SSet.{u}) ⟶
      TopCat.toSSet.obj X).app (op ⦋0⦌))
    exact ⟨SSet.stdSimplex.obj₀Equiv.symm 0, rfl⟩
  refine ⟨hx, ?_⟩
  let HS := TopCat.singularHomotopyRelAtPoint x₀ H
  let HR := SSet.realizeHomotopyRelAtVertex HS sx hx
  have hFixed := HR.eq_fst t (Set.mem_singleton_iff.mpr rfl)
  have hPoint : sSetTopAdj.counit.app X (SSet.realizedVertex sx) = x₀ := by
    simpa only [sx, Equiv.apply_symm_apply] using TopCat.counit_realizedVertex sx
  calc
    _ = sSetTopAdj.counit.app Y
        (SSet.toTop.map (TopCat.toSSet.map f) (SSet.realizedVertex sx)) :=
      congrArg (sSetTopAdj.counit.app Y) hFixed
    _ = f (sSetTopAdj.counit.app X (SSet.realizedVertex sx)) :=
      ConcreteCategory.congr_hom (sSetTopAdj.counit.naturality f) (SSet.realizedVertex sx)
    _ = f x₀ := congrArg f hPoint

end ActualStationarySingularHomotopy

end
