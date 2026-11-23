/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.FiniteCompact
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCompactSupport
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex
public import MathlibExt.Topology.Category.CGWH.Basic

/-!
# Realizations of simplicial sets land in CGWH

Every simplicial-set realization is compactly generated and weak Hausdorff,
with independent compact-probe and carrier universes.  The results are named
proof values rather than global instances; the categorical realization lift
is defined separately.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u v

namespace SSet

/-- The realization of an arbitrary simplicial set is compactly generated
for an independent compact-probe universe. -/
theorem uCompactlyGeneratedSpace_realization
    (Y : SSet.{v}) :
    UCompactlyGeneratedSpace.{u} (SSet.toTop.obj Y) := by
  apply uCompactlyGeneratedSpace_of_isClosed
  intro A hA
  let q := SSet.sigmaToTop Y
  have hq := SSet.isQuotientMap_sigmaToTop Y
  rw [← hq.isClosed_preimage]
  apply isClosed_sigma_iff.2
  intro s
  let D := Convexity.StdSimplex ℝ (Fin (s.dim + 1))
  let _ : T2Space D :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights
      ℝ (Fin (s.dim + 1))).t2Space
  let e₀ : ULift.{u} D ≃ₜ D := Homeomorph.ulift
  let _ : CompactSpace (ULift.{u} D) := e₀.symm.compactSpace
  let _ : T2Space (ULift.{u} D) := e₀.symm.t2Space
  let P : CompHaus.{u} := CompHaus.of (ULift.{u} D)
  let e : P ≃ₜ D := e₀
  let g : C(P, SSet.toTop.obj Y) :=
    ⟨fun z => q ⟨s, e z⟩,
      hq.continuous.comp (continuous_sigmaMk.comp e.continuous)⟩
  have hpre :
      g ⁻¹' A = e ⁻¹'
        ((@Sigma.mk Y.N
          (fun t : Y.N => Convexity.StdSimplex ℝ (Fin (t.dim + 1))) s) ⁻¹'
            (q ⁻¹' A)) := by
    ext z
    rfl
  exact e.isClosed_preimage.mp (hpre ▸ hA P g)

/-- The realization of an arbitrary simplicial set is weak Hausdorff for an
independent compact-probe universe. -/
theorem uWeakHausdorffSpace_realization
    (Y : SSet.{v}) :
    UWeakHausdorffSpace.{u} (SSet.toTop.obj Y) where
  isClosed_range K f := by
    let R : Set (SSet.toTop.obj Y) := Set.range f
    have hR : IsCompact R := isCompact_range f.continuous
    obtain ⟨A, hAfin, hsub⟩ :=
      SSet.exists_finite_subcomplex_of_isCompact Y R hR
    let _ : SSet.Finite (A : SSet.{v}) := hAfin
    let i : C(SSet.toTop.obj (A : SSet.{v}), SSet.toTop.obj Y) :=
      (SSet.toTop.map A.ι).hom
    have hi : Topology.IsClosedEmbedding i :=
      TopCat.closedT1Embeddings_le_isClosedEmbedding _
        (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (S := A))
    have hsub' : R ⊆ Set.range i := by
      simpa only [R, i] using hsub
    have hpreCompact : IsCompact (i ⁻¹' R) :=
      (hi.isInducing.isCompact_preimage_iff hsub').2 hR
    have hpreClosed : IsClosed (i ⁻¹' R) := hpreCompact.isClosed
    exact (hi.isClosed_iff_preimage_isClosed hsub').2 hpreClosed

end SSet
