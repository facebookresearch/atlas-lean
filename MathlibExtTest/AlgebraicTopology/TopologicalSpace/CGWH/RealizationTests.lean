/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.Realization

/-!
# Tests for arbitrary simplicial-set realization landing in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology
open scoped Simplicial

universe u v

namespace MathlibExtTest.CGWH.RealizationTests

#check SSet.uCompactlyGeneratedSpace_realization
#check SSet.uWeakHausdorffSpace_realization

section Symbolic

variable (Y : SSet.{v})

example : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj Y) :=
  SSet.uCompactlyGeneratedSpace_realization Y

example : UWeakHausdorffSpace.{u} (SSet.toTop.obj Y) :=
  SSet.uWeakHausdorffSpace_realization Y

example : CGWH.{u, v} := by
  let _ : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj Y) :=
    SSet.uCompactlyGeneratedSpace_realization Y
  let _ : UWeakHausdorffSpace.{u} (SSet.toTop.obj Y) :=
    SSet.uWeakHausdorffSpace_realization Y
  exact CGWH.of (SSet.toTop.obj Y)

end Symbolic

section UniverseMatrix

example (Y : SSet.{0}) :
    UCompactlyGeneratedSpace.{0} (SSet.toTop.obj Y) :=
  SSet.uCompactlyGeneratedSpace_realization Y

example (Y : SSet.{1}) :
    UCompactlyGeneratedSpace.{1} (SSet.toTop.obj Y) :=
  SSet.uCompactlyGeneratedSpace_realization Y

example (Y : SSet.{1}) :
    UCompactlyGeneratedSpace.{0} (SSet.toTop.obj Y) :=
  SSet.uCompactlyGeneratedSpace_realization Y

example (Y : SSet.{0}) :
    UCompactlyGeneratedSpace.{1} (SSet.toTop.obj Y) :=
  SSet.uCompactlyGeneratedSpace_realization Y

example (Y : SSet.{0}) :
    UWeakHausdorffSpace.{0} (SSet.toTop.obj Y) :=
  SSet.uWeakHausdorffSpace_realization Y

example (Y : SSet.{1}) :
    UWeakHausdorffSpace.{1} (SSet.toTop.obj Y) :=
  SSet.uWeakHausdorffSpace_realization Y

example (Y : SSet.{1}) :
    UWeakHausdorffSpace.{0} (SSet.toTop.obj Y) :=
  SSet.uWeakHausdorffSpace_realization Y

example (Y : SSet.{0}) :
    UWeakHausdorffSpace.{1} (SSet.toTop.obj Y) :=
  SSet.uWeakHausdorffSpace_realization Y

end UniverseMatrix

section CompactGenerationLeaves

example (Y : SSet.{v}) (A : Set (SSet.toTop.obj Y)) :
    IsClosed (SSet.sigmaToTop Y ⁻¹' A) ↔ IsClosed A :=
  (SSet.isQuotientMap_sigmaToTop Y).isClosed_preimage

example (Y : SSet.{v}) (s : Y.N) :
    ∃ (P : CompHaus.{u}) (g : C(P, SSet.toTop.obj Y)),
      Continuous g := by
  let D := Convexity.StdSimplex ℝ (Fin (s.dim + 1))
  let _ : T2Space D :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights
      ℝ (Fin (s.dim + 1))).t2Space
  let e₀ : ULift.{u} D ≃ₜ D := Homeomorph.ulift
  let _ : CompactSpace (ULift.{u} D) := e₀.symm.compactSpace
  let _ : T2Space (ULift.{u} D) := e₀.symm.t2Space
  let P : CompHaus.{u} := CompHaus.of (ULift.{u} D)
  let e : P ≃ₜ D := e₀
  let q := SSet.sigmaToTop Y
  have hq := SSet.isQuotientMap_sigmaToTop Y
  let g : C(P, SSet.toTop.obj Y) :=
    ⟨fun z => q ⟨s, e z⟩,
      hq.continuous.comp (continuous_sigmaMk.comp e.continuous)⟩
  exact ⟨P, g, g.continuous⟩

example (Y : SSet.{v}) (A : Set (SSet.toTop.obj Y))
    (hA : ∀ (P : CompHaus.{u}) (g : C(P, SSet.toTop.obj Y)),
      IsClosed (g ⁻¹' A)) : IsClosed A := by
  let _ : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj Y) :=
    SSet.uCompactlyGeneratedSpace_realization Y
  exact UCompactlyGeneratedSpace.isClosed hA

end CompactGenerationLeaves

section WeakHausdorffLeaves

example (Y : SSet.{v}) (R : Set (SSet.toTop.obj Y))
    (hR : IsCompact R) :
    ∃ (A : Y.Subcomplex) (_ : SSet.Finite (A : SSet.{v})),
      R ⊆ Set.range (SSet.toTop.map A.ι) ∧
        Topology.IsClosedEmbedding (SSet.toTop.map A.ι).hom := by
  obtain ⟨A, hAfin, hsub⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact Y R hR
  refine ⟨A, hAfin, hsub, ?_⟩
  exact TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (S := A))

example (Y : SSet.{v}) (K : CompHaus.{u})
    (f : C(K, SSet.toTop.obj Y)) : IsClosed (Set.range f) :=
  (SSet.uWeakHausdorffSpace_realization Y).isClosed_range K f

end WeakHausdorffLeaves

section StandardSimplices

example : UCompactlyGeneratedSpace.{u}
    (SSet.toTop.obj (Δ[0] : SSet.{v})) :=
  SSet.uCompactlyGeneratedSpace_realization _

example : UWeakHausdorffSpace.{u}
    (SSet.toTop.obj (Δ[0] : SSet.{v})) :=
  SSet.uWeakHausdorffSpace_realization _

example : UCompactlyGeneratedSpace.{u}
    (SSet.toTop.obj (Δ[1] : SSet.{v})) :=
  SSet.uCompactlyGeneratedSpace_realization _

example : UWeakHausdorffSpace.{u}
    (SSet.toTop.obj (Δ[1] : SSet.{v})) :=
  SSet.uWeakHausdorffSpace_realization _

end StandardSimplices

section Negative

variable (Y : SSet.{v})

example : True := by
  fail_if_success
    let _ : UCompactlyGeneratedSpace.{u} (SSet.toTop.obj Y) :=
      inferInstance
  fail_if_success
    let _ : UWeakHausdorffSpace.{u} (SSet.toTop.obj Y) := inferInstance
  fail_if_success
    let _ : T2Space (SSet.toTop.obj Y) := inferInstance
  trivial

#guard_msgs (error, substring := true) in
#check SSet.toCGWH

end Negative

#print axioms SSet.uCompactlyGeneratedSpace_realization
#print axioms SSet.uWeakHausdorffSpace_realization

end MathlibExtTest.CGWH.RealizationTests
