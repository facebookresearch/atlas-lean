/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Star homomorphisms of C₀ function algebras

This file supplies pointwise postcomposition of continuous functions vanishing
at infinity by a nonunital C-star homomorphism, precomposition by cocompact
maps, and the `C₀` exponential law for products. It also identifies matrices
of such functions with functions taking values in a C-star matrix algebra.
-/

@[expose] public section

open Filter Set Topology
open scoped CStarAlgebra Matrix ZeroAtInfty

noncomputable section

universe u v w

namespace ZeroAtInftyContinuousMap

/-! ## Functoriality in the coefficient algebra -/

/-- Let `Omega` be a topological space. Let `A`, `B` be possibly nonunital complex C*-algebras.

Pointwise postcomposition of a `C₀` function by a nonunital C-star homomorphism. -/
def nonUnitalStarAlgHom_postcomp
    {Omega : Type u} [TopologicalSpace Omega]
    {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) : C₀(Omega, A) →⋆ₙₐ[ℂ] C₀(Omega, B) where
  toFun f :=
    { toFun := fun omega ↦ phi (f omega)
      continuous_toFun := (map_continuous phi).comp f.continuous_toFun
      zero_at_infty' := by
        change Tendsto (phi ∘ f) (cocompact Omega) (nhds 0)
        simpa only [map_zero] using
          ((map_continuous phi).tendsto (0 : A)).comp (zero_at_infty f) }
  map_zero' := ext fun _ ↦ map_zero phi
  map_add' f g := ext fun _ ↦ map_add phi _ _
  map_mul' f g := ext fun _ ↦ map_mul phi _ _
  map_star' f := ext fun _ ↦ map_star phi _
  map_smul' scalar f := ext fun _ ↦ map_smul phi scalar _

@[simp]
theorem nonUnitalStarAlgHom_postcomp_apply
    {Omega : Type u} [TopologicalSpace Omega]
    {A : Type v} {B : Type w}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) (f : C₀(Omega, A)) (omega : Omega) :
    nonUnitalStarAlgHom_postcomp phi f omega = phi (f omega) :=
  rfl

@[simp]
theorem nonUnitalStarAlgHom_postcomp_id
    (Omega : Type u) [TopologicalSpace Omega]
    (A : Type v) [NonUnitalCStarAlgebra A] :
    nonUnitalStarAlgHom_postcomp (Omega := Omega) (NonUnitalStarAlgHom.id ℂ A) =
      NonUnitalStarAlgHom.id ℂ C₀(Omega, A) := by
  ext f omega
  rfl

/-- Let `Omega` be a topological space. Let `A`, `B`, `C` be possibly nonunital complex C*-algebras.

Postcomposition respects composition of coefficient homomorphisms. -/
theorem nonUnitalStarAlgHom_postcomp_comp
    {Omega : Type u} [TopologicalSpace Omega]
    {A : Type v} {B : Type w} {C : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (psi : B →⋆ₙₐ[ℂ] C) (phi : A →⋆ₙₐ[ℂ] B) :
    nonUnitalStarAlgHom_postcomp (Omega := Omega) (psi.comp phi) =
      (nonUnitalStarAlgHom_postcomp psi).comp
        (nonUnitalStarAlgHom_postcomp phi) := by
  ext f omega
  rfl

/-! ## Functoriality in the domain -/

/-- Let `X`, `Y` be topological spaces. Let `A` be a possibly nonunital complex C*-algebra. The
domain map is continuous and sends the cocompact filter to the cocompact filter.

Precomposition by a cocompact map as a nonunital star-algebra homomorphism. -/
def compNonUnitalStarAlgHom
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (g : CocompactMap X Y) : C₀(Y, A) →⋆ₙₐ[ℂ] C₀(X, A) :=
  { compNonUnitalAlgHom (R := ℂ) g with
    map_star' := by
      intro f
      ext x
      rfl }

@[simp]
theorem compNonUnitalStarAlgHom_apply
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (g : CocompactMap X Y) (f : C₀(Y, A)) (x : X) :
    compNonUnitalStarAlgHom g f x = f (g x) :=
  rfl

@[simp]
theorem compNonUnitalStarAlgHom_id
    (X : Type u) [TopologicalSpace X]
    (A : Type v) [NonUnitalCStarAlgebra A] :
    compNonUnitalStarAlgHom (A := A) (CocompactMap.id X) =
      NonUnitalStarAlgHom.id ℂ C₀(X, A) := by
  ext f x
  rfl

/-- Let `W`, `X`, `Y` be topological spaces. Let `A` be a possibly nonunital complex C*-algebra. The
domain map is continuous and sends the cocompact filter to the cocompact filter.

Precomposition reverses composition of cocompact domain maps. -/
theorem compNonUnitalStarAlgHom_comp
    {W : Type*} {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (g : CocompactMap X Y) (h : CocompactMap W X) :
    compNonUnitalStarAlgHom (A := A) (g.comp h) =
      (compNonUnitalStarAlgHom h).comp (compNonUnitalStarAlgHom g) := by
  ext f x
  rfl

/-- Let `X` and `Y` be topological spaces and let `A` and `B` be possibly nonunital complex
C*-algebras. Specify a continuous cocompact map `g : X → Y` and a nonunital complex star-algebra
homomorphism `φ : A → B`.

Coefficient postcomposition commutes with domain precomposition. -/
theorem nonUnitalStarAlgHom_postcomp_comp_compNonUnitalStarAlgHom
    {X : Type u} {Y : Type v} {A : Type w} {B : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (phi : A →⋆ₙₐ[ℂ] B) (g : CocompactMap X Y) :
    (nonUnitalStarAlgHom_postcomp (Omega := X) phi).comp
        (compNonUnitalStarAlgHom (A := A) g) =
      (compNonUnitalStarAlgHom (A := B) g).comp
        (nonUnitalStarAlgHom_postcomp (Omega := Y) phi) := by
  ext f x
  rfl

/-- Let `X`, `Y` be topological spaces. Let `A` be a possibly nonunital complex C*-algebra.

Precomposition by a homeomorphism, contravariantly on `C₀`. Unlike
`ContinuousMapZero.starAlgEquivPrecomp`, this acts on functions vanishing at infinity and does
not require a distinguished point in the domain. -/
def starAlgEquivPrecomp
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (h : X ≃ₜ Y) : C₀(Y, A) ≃⋆ₐ[ℂ] C₀(X, A) :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    (compNonUnitalStarAlgHom h.toCocompactMap)
    (compNonUnitalStarAlgHom h.symm.toCocompactMap)
    (by
      apply NonUnitalStarAlgHom.ext
      intro f
      ext y
      exact congrArg f (h.apply_symm_apply y))
    (by
      apply NonUnitalStarAlgHom.ext
      intro f
      ext x
      exact congrArg f (h.symm_apply_apply x))

@[simp]
theorem starAlgEquivPrecomp_apply
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (h : X ≃ₜ Y) (f : C₀(Y, A)) (x : X) :
    starAlgEquivPrecomp h f x = f (h x) :=
  rfl

@[simp]
theorem starAlgEquivPrecomp_symm_apply
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (h : X ≃ₜ Y) (f : C₀(X, A)) (y : Y) :
    (starAlgEquivPrecomp h).symm f y = f (h.symm y) :=
  rfl

@[simp]
theorem starAlgEquivPrecomp_refl
    (X : Type u) [TopologicalSpace X]
    (A : Type v) [NonUnitalCStarAlgebra A] :
    starAlgEquivPrecomp (A := A) (Homeomorph.refl X) =
      StarAlgEquiv.refl ℂ C₀(X, A) := by
  ext f x
  rfl

theorem starAlgEquivPrecomp_symm
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (h : X ≃ₜ Y) :
    (starAlgEquivPrecomp (A := A) h).symm = starAlgEquivPrecomp h.symm := by
  ext f y
  rfl

/-- Let `X`, `Y`, `Z` be topological spaces. Let `A` be a possibly nonunital complex C*-algebra.

Precomposition reverses composition of homeomorphisms. -/
theorem starAlgEquivPrecomp_trans
    {X : Type u} {Y : Type v} {Z : Type*} {A : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [NonUnitalCStarAlgebra A]
    (h : X ≃ₜ Y) (k : Y ≃ₜ Z) :
    starAlgEquivPrecomp (A := A) (h.trans k) =
      (starAlgEquivPrecomp k).trans (starAlgEquivPrecomp h) := by
  ext f x
  rfl

/-! ## The `C₀` exponential law -/

/-- Let `X` be a T₁ topological space, let `Y` be a topological space, and let `A` be a possibly
nonunital complex C*-algebra. Both function algebras consist of continuous functions vanishing
at infinity.

The `C₀` exponential law, with uncurrying as the forward action. -/
def uncurryStarAlgEquiv
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [T1Space X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A] :
    C₀(X, C₀(Y, A)) ≃⋆ₐ[ℂ] C₀(X × Y, A) := by
  have compact_uniformly_small
      {K : Set C₀(Y, A)} (hK : IsCompact K)
      {epsilon : ℝ} (hepsilon : 0 < epsilon) :
      ∀ᶠ y in cocompact Y, ∀ f ∈ K, ‖f y‖ < epsilon := by
    obtain ⟨t, _htK, htfinite, hcover⟩ :=
      hK.finite_cover_balls (half_pos hepsilon)
    have htend : ∀ᶠ y in cocompact Y, ∀ g ∈ t, ‖g y‖ < epsilon / 2 := by
      refine htfinite.eventually_all.2 ?_
      intro g _hg
      simpa only [dist_zero_right] using
        (Metric.tendsto_nhds.mp (zero_at_infty g) (epsilon / 2) (half_pos hepsilon))
    filter_upwards [htend] with y hy
    intro f hf
    obtain ⟨g, hgt, hfg⟩ := mem_iUnion₂.mp (hcover hf)
    calc
      ‖f y‖ = ‖(f y - g y) + g y‖ := by rw [sub_add_cancel]
      _ ≤ ‖f y - g y‖ + ‖g y‖ := norm_add_le _ _
      _ = dist (f y) (g y) + ‖g y‖ := by rw [dist_eq_norm]
      _ ≤ dist f.toBCF g.toBCF + ‖g y‖ :=
        add_le_add
          (BoundedContinuousFunction.dist_coe_le_dist
            (f := f.toBCF) (g := g.toBCF) y)
          (le_refl _)
      _ = dist f g + ‖g y‖ := by rw [dist_toBCF_eq_dist]
      _ < epsilon / 2 + epsilon / 2 :=
        add_lt_add (Metric.mem_ball.mp hfg) (hy g hgt)
      _ = epsilon := add_halves epsilon
  have exists_compact_tail
      (F : C₀(X × Y, A)) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
      ∃ K : Set (X × Y), IsCompact K ∧ ∀ p ∉ K, ‖F p‖ < epsilon := by
    obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.mp
      (Metric.tendsto_nhds.mp (zero_at_infty F) epsilon hepsilon)
    refine ⟨K, hK, fun p hp ↦ ?_⟩
    have hp' : dist (F p) 0 < epsilon := hKsub hp
    simpa only [dist_zero_right] using hp'
  let prodMkCocompact : X → CocompactMap Y (X × Y) := fun x ↦
    { toFun := fun y ↦ (x, y)
      continuous_toFun := continuous_const.prodMk continuous_id
      cocompact_tendsto' := by
        let h : IsClosedEmbedding (fun y : Y ↦ (x, y)) :=
          ⟨isEmbedding_prodMkRight x, by
            rw [← Set.image_univ]
            exact isClosedMap_prodMk_left x Set.univ isClosed_univ⟩
        exact h.tendsto_cocompact }
  let currySectionLocal : C₀(X × Y, A) → X → C₀(Y, A) :=
    fun F x ↦ F.comp (prodMkCocompact x)
  have continuous_section (F : C₀(X × Y, A)) : Continuous (currySectionLocal F) := by
    refine continuous_iff_continuousAt.2 fun x0 ↦ Metric.continuousAt_iff'.2 ?_
    intro epsilon hepsilon
    obtain ⟨K, hK, hout⟩ :=
      exists_compact_tail F (show 0 < epsilon / 4 by positivity)
    let Ky : Set Y := Prod.snd '' K
    have hKy : IsCompact Ky := hK.image continuous_snd
    have hsecond : Continuous (fun p : X × Y ↦ F (x0, p.2)) :=
      F.continuous_toFun.comp (continuous_const.prodMk continuous_snd)
    have hdist : Continuous (fun p : X × Y ↦ dist (F p) (F (x0, p.2))) :=
      F.continuous_toFun.dist hsecond
    have hlocal (y : Y) :
        ∀ᶠ p : X × Y in 𝓝 (x0, y),
          dist (F p) (F (x0, p.2)) < epsilon / 2 := by
      have htend' := hdist.tendsto (x0, y)
      have htend : Tendsto (fun p : X × Y ↦ dist (F p) (F (x0, p.2)))
          (𝓝 (x0, y)) (𝓝 0) := by
        simpa only [Prod.fst, Prod.snd, dist_self] using htend'
      simpa only [Set.mem_Iio] using
        htend.eventually (Iio_mem_nhds (half_pos hepsilon))
    have hnear :
        ∀ᶠ x in 𝓝 x0, ∀ y ∈ Ky,
          dist (F (x, y)) (F (x0, y)) < epsilon / 2 :=
      hKy.eventually_forall_of_forall_eventually fun y _hy ↦ by
        simpa only [Prod.fst, Prod.snd] using hlocal y
    filter_upwards [hnear] with x hx
    have hpoint : ∀ y : Y, dist (F (x, y)) (F (x0, y)) ≤ epsilon / 2 := by
      intro y
      by_cases hy : y ∈ Ky
      · exact (hx y hy).le
      · have hxy : (x, y) ∉ K := by
          intro hmem
          exact hy ⟨(x, y), hmem, rfl⟩
        have hx0y : (x0, y) ∉ K := by
          intro hmem
          exact hy ⟨(x0, y), hmem, rfl⟩
        exact (calc
          dist (F (x, y)) (F (x0, y)) ≤
              ‖F (x, y)‖ + ‖F (x0, y)‖ := dist_le_norm_add_norm _ _
          _ < epsilon / 4 + epsilon / 4 := add_lt_add (hout _ hxy) (hout _ hx0y)
          _ = epsilon / 2 := by ring).le
    have hbcf :
        dist (currySectionLocal F x).toBCF (currySectionLocal F x0).toBCF ≤ epsilon / 2 :=
      (BoundedContinuousFunction.dist_le (by positivity)).2 hpoint
    have hc0 : dist (currySectionLocal F x) (currySectionLocal F x0) ≤ epsilon / 2 := by
      simpa only [dist_toBCF_eq_dist] using hbcf
    exact hc0.trans_lt (half_lt_self hepsilon)
  have section_zeroAtInfty (F : C₀(X × Y, A)) :
      Tendsto (currySectionLocal F) (cocompact X) (𝓝 0) := by
    refine Metric.tendsto_nhds.mpr fun epsilon hepsilon ↦ ?_
    obtain ⟨K, hK, hout⟩ :=
      exists_compact_tail F (show 0 < epsilon / 2 by positivity)
    let Kx : Set X := Prod.fst '' K
    have hKx : IsCompact Kx := hK.image continuous_fst
    filter_upwards [hKx.compl_mem_cocompact] with x hx
    have hx' : x ∉ Kx := by simpa only [Set.mem_compl_iff] using hx
    have hpoint : ∀ y : Y, ‖currySectionLocal F x y‖ ≤ epsilon / 2 := by
      intro y
      apply (hout (x, y) ?_).le
      intro hmem
      exact hx' ⟨(x, y), hmem, rfl⟩
    have hbcf : ‖(currySectionLocal F x).toBCF‖ ≤ epsilon / 2 :=
      (BoundedContinuousFunction.norm_le (by positivity)).2 hpoint
    have hc0 : ‖currySectionLocal F x‖ ≤ epsilon / 2 := by
      simpa only [norm_toBCF_eq_norm] using hbcf
    simpa only [dist_zero_right] using hc0.trans_lt (half_lt_self hepsilon)
  let uncurryHom : C₀(X, C₀(Y, A)) →⋆ₙₐ[ℂ] C₀(X × Y, A) :=
    { toFun := fun f ↦
        { toFun := fun p ↦ f p.1 p.2
          continuous_toFun := by
            have htoBCF : Continuous (fun x : X ↦ (f x).toBCF) :=
              (isometry_toBCF (α := Y) (β := A)).continuous.comp
                f.continuous_toFun
            exact continuous_eval.comp (htoBCF.prodMap continuous_id)
          zero_at_infty' := by
            rw [← Filter.coprod_cocompact]
            refine Metric.tendsto_nhds.mpr fun epsilon hepsilon ↦ ?_
            have hx : {x : X | dist (f x) 0 < epsilon} ∈ cocompact X :=
              Metric.tendsto_nhds.mp (zero_at_infty f) epsilon hepsilon
            have hK : IsCompact (insert 0 (Set.range f)) :=
              (zero_at_infty f).isCompact_insert_range_of_cocompact f.continuous_toFun
            have hy : {y : Y | ∀ g ∈ insert 0 (Set.range f), ‖g y‖ < epsilon} ∈
                cocompact Y := compact_uniformly_small hK hepsilon
            change {p : X × Y | dist (f p.1 p.2) 0 < epsilon} ∈
              (cocompact X).coprod (cocompact Y)
            rw [Filter.mem_coprod_iff]
            constructor
            · refine ⟨{x : X | dist (f x) 0 < epsilon}, hx, ?_⟩
              intro p hp
              calc
                dist (f p.1 p.2) 0 ≤
                    dist (f p.1).toBCF (0 : C₀(Y, A)).toBCF := by
                  have hpdist := BoundedContinuousFunction.dist_coe_le_dist
                    (f := (f p.1).toBCF)
                    (g := (0 : C₀(Y, A)).toBCF) p.2
                  change dist (f p.1 p.2) ((0 : C₀(Y, A)) p.2) ≤
                    dist (f p.1).toBCF (0 : C₀(Y, A)).toBCF at hpdist
                  simpa only [zero_apply] using hpdist
                _ = dist (f p.1) 0 := dist_toBCF_eq_dist
                _ < epsilon := hp
            · refine ⟨{y : Y | ∀ g ∈ insert 0 (Set.range f), ‖g y‖ < epsilon}, hy, ?_⟩
              intro p hp
              change dist (f p.1 p.2) 0 < epsilon
              simpa only [dist_zero_right] using
                hp (f p.1) (mem_insert_iff.mpr (Or.inr ⟨p.1, rfl⟩)) }
      map_zero' := by ext p; rfl
      map_add' := by intro f g; ext p; rfl
      map_mul' := by intro f g; ext p; rfl
      map_star' := by intro f; ext p; rfl
      map_smul' := by intro c f; ext p; rfl }
  let curryHom : C₀(X × Y, A) →⋆ₙₐ[ℂ] C₀(X, C₀(Y, A)) :=
    { toFun := fun F ↦
        { toFun := currySectionLocal F
          continuous_toFun := continuous_section F
          zero_at_infty' := section_zeroAtInfty F }
      map_zero' := by ext x y; rfl
      map_add' := by intro F G; ext x y; rfl
      map_mul' := by intro F G; ext x y; rfl
      map_star' := by intro F; ext x y; rfl
      map_smul' := by intro c F; ext x y; rfl }
  exact StarAlgEquiv.ofNonUnitalStarAlgHom uncurryHom curryHom
    (by
      apply NonUnitalStarAlgHom.ext
      intro f
      ext x y
      rfl)
    (by
      apply NonUnitalStarAlgHom.ext
      intro F
      ext p
      rfl)

@[simp]
theorem uncurryStarAlgEquiv_apply
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [T1Space X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (f : C₀(X, C₀(Y, A))) (x : X) (y : Y) :
    uncurryStarAlgEquiv f (x, y) = f x y :=
  rfl

@[simp]
theorem uncurryStarAlgEquiv_symm_apply
    {X : Type u} {Y : Type v} {A : Type w}
    [TopologicalSpace X] [T1Space X] [TopologicalSpace Y]
    [NonUnitalCStarAlgebra A]
    (F : C₀(X × Y, A)) (x : X) (y : Y) :
    uncurryStarAlgEquiv.symm F x y = F (x, y) :=
  rfl

end ZeroAtInftyContinuousMap

namespace CStarMatrix

variable {Omega : Type u} [TopologicalSpace Omega]
variable {A : Type v} [NonUnitalCStarAlgebra A]
variable {I : Type w} [Fintype I]

local instance spectralOrderInstance : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance spectralOrderedRingInstance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- Let `Ω` be a topological space, let `A` be a possibly nonunital complex C*-algebra, and let `I`
be a finite index type. Matrices and functions vanishing at infinity have their canonical
C*-norms.

The entrywise star-algebra equivalence between matrices of `C₀` functions and `C₀` functions
with matrix values. -/
def zeroAtInftyStarAlgEquiv :
    CStarMatrix I I C₀(Omega, A) ≃⋆ₐ[ℂ] C₀(Omega, CStarMatrix I I A) := by
  let matrixToFunctions :
      CStarMatrix I I C₀(Omega, A) →⋆ₙₐ[ℂ] C₀(Omega, CStarMatrix I I A) :=
    { toFun := fun M ↦
        { toFun := fun omega i j ↦ M i j omega
          continuous_toFun := continuous_pi fun i ↦
            continuous_pi fun j ↦ (M i j).continuous_toFun
          zero_at_infty' := tendsto_pi_nhds.mpr fun i ↦
            tendsto_pi_nhds.mpr fun j ↦ zero_at_infty (M i j) }
      map_zero' := by
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        apply CStarMatrix.ext
        intro i j
        rfl
      map_add' := by
        intro M N
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        apply CStarMatrix.ext
        intro i j
        rfl
      map_mul' := by
        intro M N
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        apply CStarMatrix.ext
        intro i j
        change (∑ k, M i k * N k j) omega =
          ∑ k, M i k omega * N k j omega
        let ev : C₀(Omega, A) →+ A :=
          { toFun := fun f ↦ f omega
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        have h := map_sum ev (fun k ↦ M i k * N k j) Finset.univ
        change (∑ k, M i k * N k j) omega =
          ∑ k, M i k omega * N k j omega at h
        exact h
      map_star' := by
        intro M
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        apply CStarMatrix.ext
        intro i j
        rfl
      map_smul' := by
        intro scalar M
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        apply CStarMatrix.ext
        intro i j
        rfl }
  let entry : C₀(Omega, CStarMatrix I I A) → I → I → C₀(Omega, A) :=
    fun F i j ↦
      { toFun := fun omega ↦ F omega i j
        continuous_toFun := F.continuous_toFun.matrix_elem i j
        zero_at_infty' :=
          tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (zero_at_infty F) i) j }
  let functionsToMatrix :
      C₀(Omega, CStarMatrix I I A) →⋆ₙₐ[ℂ] CStarMatrix I I C₀(Omega, A) :=
    { toFun := fun F i j ↦ entry F i j
      map_zero' := by
        apply CStarMatrix.ext
        intro i j
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        rfl
      map_add' := by
        intro F G
        apply CStarMatrix.ext
        intro i j
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        rfl
      map_mul' := by
        intro F G
        apply CStarMatrix.ext
        intro i j
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        change (∑ k, F omega i k * G omega k j) =
          (∑ k, entry F i k * entry G k j) omega
        let ev : C₀(Omega, A) →+ A :=
          { toFun := fun f ↦ f omega
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        have h := map_sum ev (fun k ↦ entry F i k * entry G k j) Finset.univ
        change (∑ k, entry F i k * entry G k j) omega =
          ∑ k, F omega i k * G omega k j at h
        exact h.symm
      map_star' := by
        intro F
        apply CStarMatrix.ext
        intro i j
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        rfl
      map_smul' := by
        intro scalar F
        apply CStarMatrix.ext
        intro i j
        apply ZeroAtInftyContinuousMap.ext
        intro omega
        rfl }
  exact StarAlgEquiv.ofNonUnitalStarAlgHom matrixToFunctions functionsToMatrix
    (by
      apply NonUnitalStarAlgHom.ext
      intro M
      apply CStarMatrix.ext
      intro i j
      apply ZeroAtInftyContinuousMap.ext
      intro omega
      rfl)
    (by
      apply NonUnitalStarAlgHom.ext
      intro F
      apply ZeroAtInftyContinuousMap.ext
      intro omega
      apply CStarMatrix.ext
      intro i j
      rfl)

@[simp]
theorem zeroAtInftyStarAlgEquiv_apply
    (M : CStarMatrix I I C₀(Omega, A)) (omega : Omega) (i j : I) :
    zeroAtInftyStarAlgEquiv M omega i j = M i j omega :=
  rfl

@[simp]
theorem zeroAtInftyStarAlgEquiv_symm_apply
    (F : C₀(Omega, CStarMatrix I I A)) (i j : I) (omega : Omega) :
    zeroAtInftyStarAlgEquiv.symm F i j omega = F omega i j :=
  rfl

end CStarMatrix

end
