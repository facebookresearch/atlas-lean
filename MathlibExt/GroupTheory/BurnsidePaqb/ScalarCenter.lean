/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.BurnsidePaqb.KillingLemma

/-!
Scalar-center stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/ScalarCenter.lean`.
-/

namespace BurnsidePaqb

@[expose] public section

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
/-- **Characters of full absolute value have equal eigenvalues.** Let $G$ be a finite group,
$V$ a nonzero finite-dimensional complex vector space and $\rho$ an irreducible representation of
$G$ on $V$ with character $\chi$. If $g \in G$ satisfies $|\chi(g)| = \dim V$, then any two roots
of the characteristic polynomial of $\rho(g)$ are equal. -/
theorem all_roots_eq_of_norm_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] [Finite G] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (g : G)
    (h : ‖ρ.character g‖ = Module.finrank ℂ V) :
    ∀ μ₁ ∈ (ρ g).charpoly.roots, ∀ μ₂ ∈ (ρ g).charpoly.roots, μ₁ = μ₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, hne⟩ := hcon
  have hlt := abs_multiset_sum_lt _ (fun μ hμ => charpoly_root_norm_eq_one ρ g μ hμ)
    ⟨μ₁, hμ₁, μ₂, hμ₂, hne⟩
  rw [← character_eq_sum_roots ρ g, charpoly_roots_card ρ g] at hlt
  rw [h] at hlt
  exact (lt_irrefl _) hlt

omit [Fintype G] in
/-- **Elements with a single eigenvalue act as scalars.** Let $G$ be a finite group, $V$ a nonzero
finite-dimensional complex vector space, $\rho$ a representation of $G$ on $V$, $g \in G$ and
$\mu_0 \in \mathbb{C}$. If every root of the characteristic polynomial of $\rho(g)$ equals
$\mu_0$, then $\rho(g) = \mu_0 \cdot \mathrm{id}_V$. -/
theorem eq_smul_one_of_all_roots_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] [Finite G] (ρ : Representation ℂ G V) (g : G)
    (μ₀ : ℂ) (hall : ∀ μ ∈ (ρ g).charpoly.roots, μ = μ₀) :
    (ρ g : Module.End ℂ V) = μ₀ • 1 := by
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hn : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have hpow : (ρ g : Module.End ℂ V) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have haeval1 : Polynomial.aeval (ρ g : Module.End ℂ V)
      (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
    exact sub_eq_zero.mpr hpow
  have hdvd1 : minpoly ℂ (ρ g : Module.End ℂ V)
      ∣ (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ) :=
    minpoly.dvd _ _ haeval1
  have hsplit : (ρ g).charpoly.Splits := IsAlgClosed.splits _
  have hprod := hsplit.eq_prod_roots_of_monic (LinearMap.charpoly_monic _)
  have hmap : (ρ g).charpoly.roots.map (fun μ => Polynomial.X - Polynomial.C μ)
      = Multiset.replicate (Module.finrank ℂ V)
        (Polynomial.X - Polynomial.C μ₀) := by
    have hcard := charpoly_roots_card ρ g
    rw [← hcard, ← Multiset.map_const]
    apply Multiset.map_congr rfl
    intro μ hμ
    change Polynomial.X - Polynomial.C μ = Polynomial.X - Polynomial.C μ₀
    rw [hall μ hμ]
  rw [hmap, Multiset.prod_replicate] at hprod
  have hCH : Polynomial.aeval (ρ g : Module.End ℂ V) (ρ g).charpoly = 0 :=
    LinearMap.aeval_self_charpoly _
  have hdvd2 : minpoly ℂ (ρ g : Module.End ℂ V)
      ∣ (Polynomial.X - Polynomial.C μ₀) ^ Module.finrank ℂ V := by
    rw [← hprod]
    exact minpoly.dvd _ _ hCH
  have hsep : (Polynomial.X ^ orderOf g - Polynomial.C (1 : ℂ)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hn) one_ne_zero
  have hsep1 : (Polynomial.X ^ orderOf g - 1 : Polynomial ℂ).Separable := by
    have h1 := hsep
    rwa [Polynomial.C_1] at h1
  have hmsep : (minpoly ℂ (ρ g : Module.End ℂ V)).Separable :=
    hsep1.of_dvd hdvd1
  have hdvd3 : minpoly ℂ (ρ g : Module.End ℂ V) ∣ Polynomial.X - Polynomial.C μ₀ :=
    (hmsep.squarefree.dvd_pow_iff_dvd (ne_of_gt hpos)).mp hdvd2
  have hInt : IsIntegral ℂ (ρ g : Module.End ℂ V) :=
    Algebra.IsIntegral.isIntegral _
  have hmonic : (minpoly ℂ (ρ g : Module.End ℂ V)).Monic := minpoly.monic hInt
  have hmonic2 : (Polynomial.X - Polynomial.C μ₀).Monic :=
    Polynomial.monic_X_sub_C μ₀
  have hdeg : (Polynomial.X - Polynomial.C μ₀).natDegree
      ≤ (minpoly ℂ (ρ g : Module.End ℂ V)).natDegree := by
    rw [Polynomial.natDegree_X_sub_C]
    by_contra hlt
    have h0 : (minpoly ℂ (ρ g : Module.End ℂ V)).natDegree = 0 := by omega
    have heq1 : minpoly ℂ (ρ g : Module.End ℂ V) = 1 := by
      have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
      have h1 : (minpoly ℂ (ρ g : Module.End ℂ V)).coeff 0 = 1 := by
        have hlc := Polynomial.Monic.def.mp hmonic
        rw [hC, Polynomial.leadingCoeff_C] at hlc
        exact hlc
      rw [hC, h1, Polynomial.C_1]
    exact minpoly.ne_one _ _ heq1
  have heq : Polynomial.X - Polynomial.C μ₀ = minpoly ℂ (ρ g : Module.End ℂ V) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hmonic2 hdvd3 hdeg
  have haeval : Polynomial.aeval (ρ g : Module.End ℂ V)
      (Polynomial.X - Polynomial.C μ₀) = 0 := by
    rw [heq]
    exact minpoly.aeval _ _
  have hcalc : Polynomial.aeval (ρ g : Module.End ℂ V)
      (Polynomial.X - Polynomial.C μ₀)
      = (ρ g : Module.End ℂ V) - μ₀ • (1 : Module.End ℂ V) := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
  rw [hcalc] at haeval
  exact sub_eq_zero.mp haeval

/-- **Scalar center of a representation.** Let $\rho$ be a representation of a group $G$ on a
nonzero complex vector space $V$. The scalar center of $\rho$ is the subgroup of $G$ consisting of
the elements $g$ such that $\rho(g) = c \cdot \mathrm{id}_V$ for some $c \in \mathbb{C}$. -/
noncomputable def charCenter {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) : Subgroup G where
  carrier := { g | ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 }
  one_mem' := ⟨1, by rw [map_one, one_smul]⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨c₁, hc₁⟩ := ha
    obtain ⟨c₂, hc₂⟩ := hb
    refine ⟨c₁ * c₂, ?_⟩
    rw [map_mul, hc₁, hc₂, smul_mul_assoc, one_mul, smul_smul]
  inv_mem' := by
    intro g hg
    obtain ⟨c, hc⟩ := hg
    have key : (ρ g⁻¹ : Module.End ℂ V) * (ρ g : Module.End ℂ V) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [hc, mul_smul_comm, mul_one] at key
    have hc0 : c ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at key
      exact one_ne_zero key.symm
    refine ⟨c⁻¹, ?_⟩
    have hsm := congrArg (c⁻¹ • ·) key
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hsm

instance charCenter_normal {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) : (charCenter ρ).Normal where
  conj_mem := by
    intro n hn h
    obtain ⟨c, hc⟩ := hn
    refine ⟨c, ?_⟩
    have hmul : (ρ (h * n * h⁻¹) : Module.End ℂ V)
        = (ρ h : Module.End ℂ V) * (ρ n : Module.End ℂ V)
          * (ρ h⁻¹ : Module.End ℂ V) := by
      rw [map_mul, map_mul]
    have h1 : (ρ h : Module.End ℂ V) * (ρ h⁻¹ : Module.End ℂ V) = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hsc : (ρ h : Module.End ℂ V) * (c • 1) * (ρ h⁻¹ : Module.End ℂ V)
        = c • ((ρ h : Module.End ℂ V) * (ρ h⁻¹ : Module.End ℂ V)) := by
      simp only [mul_smul_comm, smul_mul_assoc, mul_one]
    rw [hmul, hc, hsc, h1]

omit [Fintype G] in
/-- **Membership in the scalar center.** Let $\rho$ be a representation of a group $G$ on a nonzero
complex vector space $V$. An element $g \in G$ lies in the scalar center of $\rho$ if and only if
$\rho(g) = c \cdot \mathrm{id}_V$ for some $c \in \mathbb{C}$. -/
theorem mem_charCenter_iff {V : Type*} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (ρ : Representation ℂ G V) (g : G) :
    g ∈ charCenter ρ ↔ ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 :=
  Iff.rfl

omit [Fintype G] in
/-- **Elements acting by a scalar lie in the scalar center.** Let $\rho$ be a representation of a
group $G$ on a nonzero complex vector space $V$. If $g \in G$ and $c \in \mathbb{C}$ satisfy
$\rho(g) = c \cdot \mathrm{id}_V$, then $g$ lies in the scalar center of $\rho$. -/
theorem mem_charCenter_of_eq_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V) (g : G) (c : ℂ)
    (hc : (ρ g : Module.End ℂ V) = c • 1) : g ∈ charCenter ρ :=
  ⟨c, hc⟩

omit [Fintype G] in
/-- **Elements of the scalar center act by scalars.** Let $\rho$ be a representation of a group $G$
on a nonzero complex vector space $V$. If $g$ lies in the scalar center of $\rho$, then there is
$c \in \mathbb{C}$ with $\rho(g) = c \cdot \mathrm{id}_V$. -/
theorem exists_eq_smul_of_mem_charCenter {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (ρ : Representation ℂ G V) (g : G) (h : g ∈ charCenter ρ) :
    ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 :=
  h

omit [Fintype G] in
/-- **The scalar center of a nonlinear irreducible representation is proper.** Let $\rho$ be an
irreducible representation of a group $G$ on a finite-dimensional complex vector space $V$ with
$\dim V > 1$. Then the scalar center of $\rho$ is a proper subgroup of $G$. -/
theorem charCenter_proper_of_nonlinear {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (h : 1 < Module.finrank ℂ V) :
    charCenter ρ ≠ ⊤ := by
  intro htop
  have hall : ∀ g : G, ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 := by
    intro g
    have hg : g ∈ charCenter ρ := htop ▸ Subgroup.mem_top g
    exact hg
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hWmem : v ∈ Submodule.span ℂ ({v} : Set V) :=
    Submodule.subset_span (Set.mem_singleton v)
  have hinv : ∀ g : G, ∀ w ∈ Submodule.span ℂ ({v} : Set V),
      (ρ g : Module.End ℂ V) w ∈ Submodule.span ℂ ({v} : Set V) := by
    intro g w hw
    obtain ⟨c, hc⟩ := hall g
    rw [hc, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.smul_mem _ c hw
  let S : Subrepresentation ρ :=
    ⟨Submodule.span ℂ ({v} : Set V), fun g _ hw => hinv g _ hw⟩
  have hSmod : S.toSubmodule = Submodule.span ℂ ({v} : Set V) := rfl
  have hbot : S ≠ ⊥ := by
    intro hS
    have h2 : S.toSubmodule = ⊥ := by rw [hS]; rfl
    rw [hSmod] at h2
    rw [h2] at hWmem
    exact hv ((Submodule.mem_bot ℂ).mp hWmem)
  have htopS : S ≠ ⊤ := by
    intro hS
    have h2 : S.toSubmodule = ⊤ := by rw [hS]; rfl
    rw [hSmod] at h2
    have hfin : Module.finrank ℂ (Submodule.span ℂ ({v} : Set V)) = 1 :=
      finrank_span_singleton hv
    have hfinW : Module.finrank ℂ (Submodule.span ℂ ({v} : Set V))
        = Module.finrank ℂ V := by
      rw [h2]
      exact finrank_top ℂ V
    omega
  exact hbot (eq_bot_or_eq_top S |>.resolve_right htopS)

omit [Fintype G] in
/-- **Elements of the scalar center have character of full absolute value.** Let $G$ be a finite
group, $V$ a nonzero finite-dimensional complex vector space and $\rho$ a representation of $G$
on $V$ with character $\chi$. If $g$ lies in the scalar center of $\rho$, then
$|\chi(g)| = \dim V$. -/
theorem norm_eq_of_mem_charCenter {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] [Finite G] (ρ : Representation ℂ G V)
    (g : G) (h : g ∈ charCenter ρ) :
    ‖ρ.character g‖ = Module.finrank ℂ V := by
  obtain ⟨c, hc⟩ := h
  have hn : orderOf g ≠ 0 := ne_of_gt (orderOf_pos g)
  have hpow : (ρ g : Module.End ℂ V) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hcpow : c ^ orderOf g = 1 := by
    have hpow' : (c ^ orderOf g) • (1 : Module.End ℂ V) = 1 := by
      have h2 := hpow
      rw [hc, smul_pow, one_pow] at h2
      exact h2
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1v : c ^ orderOf g • v = v := by
      have h3 := congrArg (· v) hpow'
      simpa using h3
    have h4 : (c ^ orderOf g - 1) • v = 0 := by
      rw [sub_smul, h1v, one_smul, sub_self]
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact sub_eq_zero.mp h5
    · exact absurd h5 hv
  have hc1 : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hcpow hn
  have htr : ρ.character g = (Module.finrank ℂ V : ℂ) * c := by
    change LinearMap.trace ℂ V (ρ g) = _
    rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]
  rw [htr, norm_mul, hc1, Complex.norm_natCast, mul_one]

end

end BurnsidePaqb
