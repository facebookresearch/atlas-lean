/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Continuous.ContinuousCocycleRepresentative
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.UniformSpace.DiscreteUniformity

/-!
# Fin-indexed finite-quotient factorization

A continuous map from a finite power of a compact totally disconnected
topological group to a discrete uniform space is invariant under coordinatewise
right multiplication by one open normal subgroup.  It therefore factors
uniquely through the corresponding finite power of the quotient group.

The familiar unary through quaternary APIs are compatibility corollaries of
the `Fin n` theorem.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Filter

namespace ContinuousCohomology

/-- Joint continuity obtained by uncurrying a continuous binary family over
a locally compact parameter space. -/
theorem continuous_uncurry_two
    {G D : Type*} [TopologicalSpace G] [TopologicalSpace D]
    [LocallyCompactSpace G] (f : C(G, C(G, D))) :
    Continuous (fun p : G × G => f p.1 p.2) :=
  ContinuousMap.continuous_uncurry_of_continuous f

/-- Joint continuity obtained by uncurrying a continuous ternary family over
locally compact parameter spaces. -/
theorem continuous_uncurry_three
    {G D : Type*} [TopologicalSpace G] [TopologicalSpace D]
    [LocallyCompactSpace G] (f : C(G, C(G, C(G, D)))) :
    Continuous (fun p : G × (G × G) => f p.1 p.2.1 p.2.2) := by
  let f₁ : C(G × G, C(G, D)) :=
    ⟨fun p => f p.1 p.2, ContinuousMap.continuous_uncurry_of_continuous f⟩
  have hf₁ : Continuous (fun p : (G × G) × G => f₁ p.1 p.2) :=
    ContinuousMap.continuous_uncurry_of_continuous f₁
  have hassoc : Continuous (fun p : G × (G × G) =>
      ((p.1, p.2.1), p.2.2)) :=
    (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  exact hf₁.comp hassoc

/-- Joint continuity obtained by uncurrying a continuous four-variable
family over locally compact parameter spaces. -/
theorem continuous_uncurry_four
    {G D : Type*} [TopologicalSpace G] [TopologicalSpace D]
    [LocallyCompactSpace G] (f : C(G, C(G, C(G, C(G, D))))) :
    Continuous (fun p : G × (G × (G × G)) =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let f₁ : C(G × (G × G), C(G, D)) :=
    ⟨fun p => f p.1 p.2.1 p.2.2, continuous_uncurry_three f⟩
  have hf₁ : Continuous (fun p : (G × (G × G)) × G => f₁ p.1 p.2) :=
    ContinuousMap.continuous_uncurry_of_continuous f₁
  have hassoc : Continuous (fun p : G × (G × (G × G)) =>
      ((p.1, (p.2.1, p.2.2.1)), p.2.2.2)) := by
    fun_prop
  exact hf₁.comp hassoc

variable {G D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [TotallyDisconnectedSpace G]
variable [UniformSpace D] [DiscreteUniformity D]

/-- A continuous map on a compact totally disconnected group is invariant
under right multiplication by an open normal subgroup. -/
private theorem exists_openNormalSubgroup_right_invariant_of_compact
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P]
    (c : P → D) (hc : Continuous c) :
    ∃ J : OpenNormalSubgroup P,
      ∀ x h : P, h ∈ J → c (x * h) = c x := by
  let _ : UniformSpace P := IsTopologicalGroup.rightUniformSpace P
  let _ : IsUniformGroup P := IsUniformGroup.of_compactSpace
  have huc : UniformContinuous c :=
    CompactSpace.uniformContinuous_of_continuous hc
  have hrel := huc (DiscreteUniformity.relId_mem_uniformity D)
  rw [Filter.mem_map] at hrel
  change {q : P × P | c q.1 = c q.2} ∈ uniformity P at hrel
  rw [uniformity_eq_comap_nhds_one', Filter.mem_comap] at hrel
  obtain ⟨U, hU, hUrel⟩ := hrel
  obtain ⟨W, hWU, hWopen, hWone⟩ := mem_nhds_iff.mp hU
  obtain ⟨J, hJW⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen hWone
  refine ⟨J, ?_⟩
  intro x h hh
  have hconj : x * h * x⁻¹ ∈ J :=
    (inferInstance : (J : Subgroup P).Normal).conj_mem h hh x
  have hpair : (x, x * h) ∈ (fun p : P × P => p.2 * p.1⁻¹) ⁻¹' U := by
    exact hWU (hJW hconj)
  have hout : c x = c (x * h) := hUrel hpair
  exact hout.symm

/-- A continuous map on a finite power is invariant under coordinatewise
right multiplication by one open normal subgroup. -/
theorem exists_openNormalSubgroup_right_invariant_fin
    {n : ℕ} (c : (Fin n → G) → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∀ x h : Fin n → G, (∀ i, h i ∈ H) → c (x * h) = c x := by
  obtain ⟨J, hJ⟩ :=
    exists_openNormalSubgroup_right_invariant_of_compact c hc
  have hJnhds : (J : Set (Fin n → G)) ∈ nhds (1 : Fin n → G) :=
    J.isOpen.mem_nhds J.one_mem
  rw [nhds_pi, Filter.mem_pi] at hJnhds
  obtain ⟨I, hIfin, U, hU, hIU⟩ := hJnhds
  let W : Set G := ⋂ i ∈ I, U i
  have hWnhds : W ∈ nhds (1 : G) := by
    exact (Filter.biInter_mem hIfin).2 fun i _ => hU i
  obtain ⟨V, hVW, hVopen, hVone⟩ := mem_nhds_iff.mp hWnhds
  obtain ⟨H, hHV⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVopen hVone
  refine ⟨H, ?_⟩
  intro x h hh
  apply hJ x h
  apply hIU
  intro i hi
  have hmem : h i ∈ W := hVW (hHV (hh i))
  exact Set.mem_iInter₂.mp hmem i hi

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [UniformSpace D] [DiscreteUniformity D] in
/-- A function on a finite power of quotient groups is uniquely determined by
its values on coordinatewise quotient representatives. -/
theorem quotient_factor_fin_unique
    {n : ℕ} (H : OpenNormalSubgroup G)
    {c : (Fin n → G) → D}
    {cbar cbar' : (Fin n → G ⧸ H.toSubgroup) → D}
    (hcbar : ∀ x,
      cbar (fun i => QuotientGroup.mk' H.toSubgroup (x i)) = c x)
    (hcbar' : ∀ x,
      cbar' (fun i => QuotientGroup.mk' H.toSubgroup (x i)) = c x) :
    cbar = cbar' := by
  funext q
  obtain ⟨x, rfl⟩ := Function.Surjective.piMap
    (fun _ : Fin n => QuotientGroup.mk'_surjective H.toSubgroup) q
  change cbar (fun i => QuotientGroup.mk' H.toSubgroup (x i)) =
    cbar' (fun i => QuotientGroup.mk' H.toSubgroup (x i))
  rw [hcbar, hcbar']

/-- A continuous map on a finite power factors through the corresponding
finite power of one finite quotient. -/
theorem exists_openNormalSubgroup_quotient_factor_fin
    {n : ℕ} (c : (Fin n → G) → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∃ cbar : (Fin n → G ⧸ H.toSubgroup) → D,
        ∀ x, cbar (fun i => QuotientGroup.mk' H.toSubgroup (x i)) = c x := by
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_right_invariant_fin c hc
  let r : Fin n → Setoid G := fun _ => QuotientGroup.leftRel H.toSubgroup
  let e := Setoid.piQuotientEquiv r
  let cquot := Quotient.lift c (by
      intro a b (hab : ∀ i,
        QuotientGroup.leftRel H.toSubgroup (a i) (b i))
      let h : Fin n → G := fun i => (a i)⁻¹ * b i
      have hh : ∀ i, h i ∈ H := fun i =>
        QuotientGroup.leftRel_apply.mp (hab i)
      have hb : b = a * h := by
        funext i
        dsimp only [h]
        change b i = a i * ((a i)⁻¹ * b i)
        group
      rw [hb]
      exact (hH a h hh).symm)
  let cbar : (Fin n → G ⧸ H.toSubgroup) → D := fun q => cquot (e q)
  refine ⟨H, cbar, ?_⟩
  intro x
  have he : e (fun i => QuotientGroup.mk' H.toSubgroup (x i)) =
      Quotient.mk'' x := by
    apply Quotient.sound
    intro i
    change QuotientGroup.leftRel H.toSubgroup
      ((QuotientGroup.mk' H.toSubgroup (x i)).out) (x i)
    rw [← Quotient.eq'']
    exact Quotient.out_eq _
  change cquot (e (fun i => QuotientGroup.mk' H.toSubgroup (x i))) = c x
  rw [he]
  rfl

/-- A continuous map from a finite power to a space with its already-selected
discrete topology factors through one finite quotient.  The discrete
uniformity used by `exists_openNormalSubgroup_quotient_factor_fin` is
installed only inside the proof, with its induced topology replaced by the
selected topology. -/
theorem exists_openNormalSubgroup_quotient_factor_fin_of_discreteTopology
    {G : Type*} {D : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [TopologicalSpace D] [DiscreteTopology D]
    {n : ℕ} (c : (Fin n → G) → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∃ cbar : (Fin n → G ⧸ H.toSubgroup) → D,
        ∀ x, cbar (fun i ↦ QuotientGroup.mk' H.toSubgroup (x i)) = c x := by
  let uD : UniformSpace D := ⊥
  have htop : (inferInstance : TopologicalSpace D) =
      uD.toTopologicalSpace := by
    change (inferInstance : TopologicalSpace D) =
      (⊥ : UniformSpace D).toTopologicalSpace
    exact (@DiscreteTopology.eq_bot D _ inferInstance).trans
      UniformSpace.toTopologicalSpace_bot.symm
  let _ : UniformSpace D := uD.replaceTopology htop
  let _ : DiscreteUniformity D :=
    ⟨UniformSpace.replaceTopology_eq uD htop⟩
  exact exists_openNormalSubgroup_quotient_factor_fin c hc

/-- Unary compatibility specialization. -/
theorem exists_openNormalSubgroup_right_invariant_one
    (c : G → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∀ g h : G, h ∈ H → c (g * h) = c g := by
  let c' : (Fin 1 → G) → D := fun x => c (x 0)
  have hc' : Continuous c' := hc.comp (continuous_apply 0)
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_right_invariant_fin c' hc'
  refine ⟨H, ?_⟩
  intro g h hh
  simpa [c'] using hH ![g] ![h] (by
    intro i
    fin_cases i
    exact hh)

/-- Binary compatibility specialization. -/
theorem exists_openNormalSubgroup_right_invariant_two
    (c : G × G → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∀ g₁ g₂ h₁ h₂ : G, h₁ ∈ H → h₂ ∈ H →
        c (g₁ * h₁, g₂ * h₂) = c (g₁, g₂) := by
  let c' : (Fin 2 → G) → D := fun x => c (x 0, x 1)
  have hc' : Continuous c' := by
    dsimp only [c']
    fun_prop
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_right_invariant_fin c' hc'
  refine ⟨H, ?_⟩
  intro g₁ g₂ h₁ h₂ hh₁ hh₂
  simpa [c'] using hH ![g₁, g₂] ![h₁, h₂] (by
    intro i
    fin_cases i
    · exact hh₁
    · exact hh₂)

/-- Ternary compatibility specialization. -/
theorem exists_openNormalSubgroup_right_invariant_three
    (c : G × (G × G) → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∀ g₁ g₂ g₃ h₁ h₂ h₃ : G,
        h₁ ∈ H → h₂ ∈ H → h₃ ∈ H →
          c (g₁ * h₁, (g₂ * h₂, g₃ * h₃)) = c (g₁, (g₂, g₃)) := by
  let c' : (Fin 3 → G) → D := fun x => c (x 0, (x 1, x 2))
  have hc' : Continuous c' := by
    dsimp only [c']
    fun_prop
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_right_invariant_fin c' hc'
  refine ⟨H, ?_⟩
  intro g₁ g₂ g₃ h₁ h₂ h₃ hh₁ hh₂ hh₃
  simpa [c'] using hH ![g₁, g₂, g₃] ![h₁, h₂, h₃] (by
    intro i
    fin_cases i
    · exact hh₁
    · exact hh₂
    · exact hh₃)

/-- Quaternary compatibility specialization. -/
theorem exists_openNormalSubgroup_right_invariant_four
    (c : G × (G × (G × G)) → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∀ g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ : G,
        h₁ ∈ H → h₂ ∈ H → h₃ ∈ H → h₄ ∈ H →
          c (g₁ * h₁, (g₂ * h₂, (g₃ * h₃, g₄ * h₄))) =
            c (g₁, (g₂, (g₃, g₄))) := by
  let c' : (Fin 4 → G) → D := fun x => c (x 0, (x 1, (x 2, x 3)))
  have hc' : Continuous c' := by
    dsimp only [c']
    fun_prop
  obtain ⟨H, hH⟩ := exists_openNormalSubgroup_right_invariant_fin c' hc'
  refine ⟨H, ?_⟩
  intro g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ hh₁ hh₂ hh₃ hh₄
  simpa [c'] using hH ![g₁, g₂, g₃, g₄] ![h₁, h₂, h₃, h₄] (by
    intro i
    fin_cases i
    · exact hh₁
    · exact hh₂
    · exact hh₃
    · exact hh₄)

/-- Unary quotient-factorization compatibility specialization. -/
theorem exists_openNormalSubgroup_quotient_factor_one
    (c : G → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G, ∃ cbar : (G ⧸ H.toSubgroup) → D,
      ∀ g : G, cbar (QuotientGroup.mk' H.toSubgroup g) = c g := by
  let c' : (Fin 1 → G) → D := fun x => c (x 0)
  have hc' : Continuous c' := hc.comp (continuous_apply 0)
  obtain ⟨H, cfin, hcfin⟩ :=
    exists_openNormalSubgroup_quotient_factor_fin c' hc'
  let cbar : (G ⧸ H.toSubgroup) → D := fun q => cfin ![q]
  refine ⟨H, cbar, ?_⟩
  intro g
  change cfin ![QuotientGroup.mk' H.toSubgroup g] = c g
  convert hcfin ![g] using 1
  · apply congrArg cfin
    funext i
    fin_cases i
    rfl
  · simp [c']

/-- Binary quotient-factorization compatibility specialization. -/
theorem exists_openNormalSubgroup_quotient_factor_two
    (c : G × G → D) (hc : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      ∃ cbar : (G ⧸ H.toSubgroup) × (G ⧸ H.toSubgroup) → D,
      ∀ g₁ g₂ : G,
        cbar (QuotientGroup.mk' H.toSubgroup g₁,
          QuotientGroup.mk' H.toSubgroup g₂) = c (g₁, g₂) := by
  let c' : (Fin 2 → G) → D := fun x => c (x 0, x 1)
  have hc' : Continuous c' := by
    dsimp only [c']
    fun_prop
  obtain ⟨H, cfin, hcfin⟩ :=
    exists_openNormalSubgroup_quotient_factor_fin c' hc'
  let cbar : (G ⧸ H.toSubgroup) × (G ⧸ H.toSubgroup) → D :=
    fun q => cfin ![q.1, q.2]
  refine ⟨H, cbar, ?_⟩
  intro g₁ g₂
  change cfin ![QuotientGroup.mk' H.toSubgroup g₁,
    QuotientGroup.mk' H.toSubgroup g₂] = c (g₁, g₂)
  convert hcfin ![g₁, g₂] using 1
  · apply congrArg cfin
    funext i
    fin_cases i <;> rfl
  · simp [c']

end ContinuousCohomology
