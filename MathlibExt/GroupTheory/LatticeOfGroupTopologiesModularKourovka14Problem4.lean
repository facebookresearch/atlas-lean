/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Topology.Algebra.Group.GroupTopology
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# A countable nilpotent group with modular lattice of group topologies (Kourovka Problem 14.4(b))

Kourovka Notebook, Problem 14.4 (V. I. Arnautov): (a) is there a nilpotent group `G` whose lattice
`𝓛(G)` of all group topologies is not modular? (b) is `𝓛(G)` non-modular for every countable
nilpotent non-abelian group `G`?

`countableNilpotentNonabelianTopologyLatticeNotModular_refuted` answers (b) in the negative. The
group is D. Peng's example `H × F` (Theorem 1.1 of the paper cited below), where `H` is the direct
sum of countably many copies of `ℤ/pℤ` and `F` is a finite non-abelian nilpotent group of order
prime to `p`. We take `p = 3`, `H = Multiplicative (ℕ →₀ ZMod 3)` and the dihedral group `F` of
order `8`, so `h ^ 3 = 1` on `H` and `(f ^ 3) ^ 3 = f` on `F`. The proof has two steps.

* Every group topology on `H × F` has small invariant neighbourhoods: each neighbourhood of `1`
  contains a neighbourhood of `1` invariant under conjugation. As in Peng's proof, let `N` be the
  closure of `{1}` and `N₂ = {f ∈ F | (1, f) ∈ N}`, a normal subgroup of `F`. The subgroup
  `K = H × N₂` is the preimage of `N` under the continuous map `g ↦ g ^ 3`, so it is closed, and it
  has finite index, so it is open. Open sets are unions of cosets of `N`, so an open neighbourhood
  `U ⊆ K` of `1` is stable under right multiplication by `{1} × N₂`; since `H` is central and `N₂`
  is normal, `U` is invariant under conjugation.
* If every group topology on a group has small invariant neighbourhoods, then its lattice of group
  topologies is modular. For two such topologies `τ` and `σ`, the products `U * V` of invariant
  neighbourhoods of `1` form a group filter basis whose topology is coarser than `τ` and `σ`, so
  each `U * V` is a neighbourhood of `1` for `τ ⊔ σ`, while the neighbourhoods of `1` for `τ ⊓ σ`
  are the intersections of those for `τ` and `σ`. If `a ≤ c`, a neighbourhood `W` of `1` for
  `a ⊔ (b ⊓ c)` then contains `(U * V) ∩ C` for suitable neighbourhoods `U`, `V`, `C` of `1` for
  `a`, `b`, `c`.

The second step replaces Peng's decomposition of `𝓛(H × F)` as the product of `𝓛(H)` and `𝓛(F)`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.4 (V. I. Arnautov). UnsolvedMath record
UM-00700989 (`KOU-14.4`), dataset ulamai/UnsolvedMath v1.8.0. The example and the first step of
the proof follow D. Peng, On the lattice of group topologies, preprint, arXiv:2310.08269v2 (2025),
Theorem 1.1 and its proof.

`𝓛(G)` is the lattice of all (not necessarily Hausdorff) group topologies, Mathlib's `GroupTopology
G`; modularity does not depend on the direction of the order. In (b) "countable" is read as
countably infinite, as in the resolving paper: for a finite group the group topologies correspond to
normal subgroups, a modular lattice, so with finite groups (b) would fail for `Q₈`.
-/

/-- **Kourovka Problem 14.4(b) (countable nilpotent groups).** This proposition states that for
every countably infinite non-abelian nilpotent group $G$, the lattice $\mathcal{L}(G)$ of all (not
necessarily Hausdorff) group topologies on $G$ is not modular. -/
def countableNilpotentNonabelianTopologyLatticeNotModular : Prop :=
  ∀ (G : Type) [Group G], Countable G → Infinite G → Group.IsNilpotent G →
    (∃ x y : G, x * y ≠ y * x) → ¬ IsModularLattice (GroupTopology G)

open Filter
open scoped Pointwise

/-! ### Group topologies with small invariant neighbourhoods -/

section SmallInvariantNhds

variable {G : Type*} [Group G]

/-- A set invariant under conjugation. -/
private def IsConjInvariant (U : Set G) : Prop :=
  ∀ g x, x ∈ U → g * x * g⁻¹ ∈ U

/-- The neighbourhood filter of `1` for a group topology. -/
private def nhdsOne (τ : GroupTopology G) : Filter G :=
  @nhds G τ.toTopologicalSpace 1

/-- A group topology has small invariant neighbourhoods if every neighbourhood of `1` contains a
neighbourhood of `1` invariant under conjugation. -/
private def HasSmallInvariantNhds (τ : GroupTopology G) : Prop :=
  ∀ U ∈ nhdsOne τ, ∃ V ∈ nhdsOne τ, V ⊆ U ∧ IsConjInvariant V

/-- Group topologies are compared through their neighbourhoods of `1`. -/
private theorem le_iff_nhdsOne {τ σ : GroupTopology G} : τ ≤ σ ↔ nhdsOne τ ≤ nhdsOne σ := by
  rw [← GroupTopology.toTopologicalSpace_le, le_iff_nhds]
  refine ⟨fun h => h 1, fun h x => ?_⟩
  rw [← @map_mul_left_nhds_one G τ.toTopologicalSpace _ τ.toIsTopologicalGroup x,
    ← @map_mul_left_nhds_one G σ.toTopologicalSpace _ σ.toIsTopologicalGroup x]
  exact map_mono h

private theorem nhdsOne_inf (τ σ : GroupTopology G) :
    nhdsOne (τ ⊓ σ) = nhdsOne τ ⊓ nhdsOne σ := by
  unfold nhdsOne
  rw [GroupTopology.toTopologicalSpace_inf]
  exact nhds_inf

private theorem one_mem_of_mem_nhdsOne {τ : GroupTopology G} {U : Set G} (hU : U ∈ nhdsOne τ) :
    (1 : G) ∈ U :=
  @mem_of_mem_nhds G τ.toTopologicalSpace 1 U hU

private theorem exists_mul_subset_of_mem_nhdsOne {τ : GroupTopology G} {U : Set G}
    (hU : U ∈ nhdsOne τ) : ∃ V ∈ nhdsOne τ, V * V ⊆ U := by
  let := τ.toTopologicalSpace
  have := τ.toIsTopologicalGroup
  obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_mul_subset hU
  exact ⟨V, hVo.mem_nhds hV1, hVU⟩

private theorem inv_mem_nhdsOne {τ : GroupTopology G} {U : Set G} (hU : U ∈ nhdsOne τ) :
    U⁻¹ ∈ nhdsOne τ := by
  let := τ.toTopologicalSpace
  have := τ.toIsTopologicalGroup
  exact inv_mem_nhds_one G hU

private theorem exists_inv_mul_subset_of_mem_nhdsOne {τ : GroupTopology G} {U : Set G}
    (hU : U ∈ nhdsOne τ) : ∃ V ∈ nhdsOne τ, V⁻¹ * V ⊆ U := by
  obtain ⟨V, hV, hVU⟩ := exists_mul_subset_of_mem_nhdsOne hU
  refine ⟨V ∩ V⁻¹, inter_mem hV (inv_mem_nhdsOne hV), ?_⟩
  exact (Set.mul_subset_mul (Set.inv_subset.2 Set.inter_subset_right)
    Set.inter_subset_left).trans hVU

private theorem IsConjInvariant.inter {U V : Set G} (hU : IsConjInvariant U)
    (hV : IsConjInvariant V) : IsConjInvariant (U ∩ V) :=
  fun g x hx => ⟨hU g x hx.1, hV g x hx.2⟩

private theorem IsConjInvariant.inv {U : Set G} (hU : IsConjInvariant U) :
    IsConjInvariant U⁻¹ := by
  intro g x hx
  rw [Set.mem_inv] at hx ⊢
  simpa [mul_assoc] using hU g x⁻¹ hx

private theorem IsConjInvariant.mul {U V : Set G} (hU : IsConjInvariant U)
    (hV : IsConjInvariant V) : IsConjInvariant (U * V) := by
  rintro g _ ⟨u, hu, v, hv, rfl⟩
  exact ⟨g * u * g⁻¹, hU g u hu, g * v * g⁻¹, hV g v hv, by group⟩

/-- An invariant set commutes past any set on its left. -/
private theorem IsConjInvariant.mul_subset {U V : Set G} (hU : IsConjInvariant U) :
    V * U ⊆ U * V := by
  rintro _ ⟨v, hv, u, hu, rfl⟩
  exact ⟨v * u * v⁻¹, hU v u hu, v, hv, by group⟩

/-- The group filter basis of the products `U * V` of invariant neighbourhoods of `1` for two group
topologies with small invariant neighbourhoods. -/
@[instance_reducible]
private def joinBasis (τ σ : GroupTopology G) (hτ : HasSmallInvariantNhds τ)
    (hσ : HasSmallInvariantNhds σ) : GroupFilterBasis G where
  sets := {W | ∃ U ∈ nhdsOne τ, ∃ V ∈ nhdsOne σ, IsConjInvariant U ∧ IsConjInvariant V ∧
    U * V = W}
  nonempty := ⟨Set.univ * Set.univ, Set.univ, univ_mem, Set.univ, univ_mem,
    fun _ _ _ => trivial, fun _ _ _ => trivial, rfl⟩
  inter_sets := by
    rintro _ _ ⟨U₁, hU₁, V₁, hV₁, cU₁, cV₁, rfl⟩ ⟨U₂, hU₂, V₂, hV₂, cU₂, cV₂, rfl⟩
    exact ⟨(U₁ ∩ U₂) * (V₁ ∩ V₂), ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, V₁ ∩ V₂, inter_mem hV₁ hV₂,
      cU₁.inter cU₂, cV₁.inter cV₂, rfl⟩,
      Set.subset_inter (Set.mul_subset_mul Set.inter_subset_left Set.inter_subset_left)
        (Set.mul_subset_mul Set.inter_subset_right Set.inter_subset_right)⟩
  one' := by
    rintro _ ⟨U, hU, V, hV, -, -, rfl⟩
    exact ⟨1, one_mem_of_mem_nhdsOne hU, 1, one_mem_of_mem_nhdsOne hV, one_mul 1⟩
  mul' := by
    rintro _ ⟨U, hU, V, hV, -, -, rfl⟩
    obtain ⟨U₀, hU₀, hU₀U⟩ := exists_mul_subset_of_mem_nhdsOne hU
    obtain ⟨V₀, hV₀, hV₀V⟩ := exists_mul_subset_of_mem_nhdsOne hV
    obtain ⟨U', hU', hU'U₀, cU'⟩ := hτ U₀ hU₀
    obtain ⟨V', hV', hV'V₀, cV'⟩ := hσ V₀ hV₀
    refine ⟨U' * V', ⟨U', hU', V', hV', cU', cV', rfl⟩, ?_⟩
    calc U' * V' * (U' * V') = U' * (V' * U') * V' := by simp only [mul_assoc]
      _ ⊆ U' * (U' * V') * V' :=
        Set.mul_subset_mul_right (Set.mul_subset_mul_left cU'.mul_subset)
      _ = (U' * U') * (V' * V') := by simp only [mul_assoc]
      _ ⊆ U * V := Set.mul_subset_mul ((Set.mul_subset_mul hU'U₀ hU'U₀).trans hU₀U)
        ((Set.mul_subset_mul hV'V₀ hV'V₀).trans hV₀V)
  inv' := by
    rintro _ ⟨U, hU, V, hV, cU, cV, rfl⟩
    refine ⟨U⁻¹ * V⁻¹, ⟨U⁻¹, inv_mem_nhdsOne hU, V⁻¹, inv_mem_nhdsOne hV, cU.inv, cV.inv, rfl⟩,
      ?_⟩
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_preimage, mul_inv_rev]
    exact cU.mul_subset ⟨b⁻¹, hb, a⁻¹, ha, rfl⟩
  conj' := by
    rintro x₀ _ ⟨U, hU, V, hV, cU, cV, rfl⟩
    exact ⟨U * V, ⟨U, hU, V, hV, cU, cV, rfl⟩, fun x hx => cU.mul cV x₀ x hx⟩

/-- The group topology of `joinBasis`. -/
private def joinTopology (τ σ : GroupTopology G) (hτ : HasSmallInvariantNhds τ)
    (hσ : HasSmallInvariantNhds σ) : GroupTopology G where
  toTopologicalSpace := (joinBasis τ σ hτ hσ).topology
  toIsTopologicalGroup := (joinBasis τ σ hτ hσ).isTopologicalGroup

private theorem nhdsOne_joinTopology (τ σ : GroupTopology G) (hτ : HasSmallInvariantNhds τ)
    (hσ : HasSmallInvariantNhds σ) :
    nhdsOne (joinTopology τ σ hτ hσ) = (joinBasis τ σ hτ hσ).toFilterBasis.filter :=
  (joinBasis τ σ hτ hσ).nhds_one_eq

private theorem left_le_joinTopology (τ σ : GroupTopology G) (hτ : HasSmallInvariantNhds τ)
    (hσ : HasSmallInvariantNhds σ) : τ ≤ joinTopology τ σ hτ hσ := by
  rw [le_iff_nhdsOne, nhdsOne_joinTopology]
  intro W hW
  rw [FilterBasis.mem_filter_iff] at hW
  obtain ⟨_, ⟨U, hU, V, hV, -, -, rfl⟩, hW⟩ := hW
  exact mem_of_superset hU fun u hu => hW ⟨u, hu, 1, one_mem_of_mem_nhdsOne hV, mul_one u⟩

private theorem right_le_joinTopology (τ σ : GroupTopology G) (hτ : HasSmallInvariantNhds τ)
    (hσ : HasSmallInvariantNhds σ) : σ ≤ joinTopology τ σ hτ hσ := by
  rw [le_iff_nhdsOne, nhdsOne_joinTopology]
  intro W hW
  rw [FilterBasis.mem_filter_iff] at hW
  obtain ⟨_, ⟨U, hU, V, hV, -, -, rfl⟩, hW⟩ := hW
  exact mem_of_superset hV fun v hv => hW ⟨1, one_mem_of_mem_nhdsOne hU, v, hv, one_mul v⟩

/-- The product of invariant neighbourhoods of `1` for `τ` and `σ` is a neighbourhood of `1` for
the join `τ ⊔ σ`. -/
private theorem mul_mem_nhdsOne_sup {τ σ : GroupTopology G} (hτ : HasSmallInvariantNhds τ)
    (hσ : HasSmallInvariantNhds σ) {U V : Set G} (hU : U ∈ nhdsOne τ) (hV : V ∈ nhdsOne σ)
    (cU : IsConjInvariant U) (cV : IsConjInvariant V) : U * V ∈ nhdsOne (τ ⊔ σ) := by
  have hle : τ ⊔ σ ≤ joinTopology τ σ hτ hσ :=
    sup_le (left_le_joinTopology τ σ hτ hσ) (right_le_joinTopology τ σ hτ hσ)
  apply le_iff_nhdsOne.1 hle
  rw [nhdsOne_joinTopology]
  exact (joinBasis τ σ hτ hσ).toFilterBasis.mem_filter_of_mem ⟨U, hU, V, hV, cU, cV, rfl⟩

/-- If every group topology on `G` has small invariant neighbourhoods, then the lattice of group
topologies on `G` is modular. -/
private theorem isModularLattice_of_forall_hasSmallInvariantNhds
    (h : ∀ τ : GroupTopology G, HasSmallInvariantNhds τ) :
    IsModularLattice (GroupTopology G) := by
  refine ⟨@fun a b c hac => ?_⟩
  rw [le_iff_nhdsOne, nhdsOne_inf]
  intro W hW
  obtain ⟨W', hW', hW'W⟩ := exists_mul_subset_of_mem_nhdsOne hW
  have hW'a : W' ∈ nhdsOne a := le_iff_nhdsOne.1 le_sup_left hW'
  have hW'bc : W' ∈ nhdsOne (b ⊓ c) := le_iff_nhdsOne.1 le_sup_right hW'
  rw [nhdsOne_inf, mem_inf_iff_superset] at hW'bc
  obtain ⟨V, hV, C₀, hC₀, hVC₀⟩ := hW'bc
  obtain ⟨C₁, hC₁, hC₁C₀⟩ := exists_inv_mul_subset_of_mem_nhdsOne hC₀
  obtain ⟨U, hU, hUsub, cU⟩ := h a (W' ∩ C₁) (inter_mem hW'a (le_iff_nhdsOne.1 hac hC₁))
  obtain ⟨V', hV', hV'V, cV'⟩ := h b V hV
  refine mem_of_superset (inter_mem_inf (mul_mem_nhdsOne_sup (h a) (h b) hU hV' cU cV') hC₁) ?_
  rintro _ ⟨⟨u, hu, v, hv, rfl⟩, hx⟩
  have hvC₀ : v ∈ C₀ := by
    have : u⁻¹ * (u * v) ∈ C₀ := hC₁C₀ ⟨u⁻¹, Set.inv_mem_inv.2 (hUsub hu).2, u * v, hx, rfl⟩
    simpa using this
  exact hW'W ⟨u, (hUsub hu).1, v, hVC₀ ⟨hV'V hv, hvC₀⟩, rfl⟩

end SmallInvariantNhds

/-! ### Products of an abelian group of exponent `p` and a finite group -/

/-- In a topological group, an open set is stable under right multiplication by the closure of
`{1}`. -/
private theorem mul_mem_of_mem_closure_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Set G} (hV : IsOpen V) {x n : G} (hx : x ∈ V)
    (hn : n ∈ closure ({1} : Set G)) : x * n ∈ V := by
  have h1 : (1 : G) ⤳ n := specializes_iff_mem_closure.2 hn
  have h2 : (x * n) ⤳ (x * 1) := h1.symm.map (continuous_const_mul x)
  rw [mul_one] at h2
  exact h2.mem_open hV hx

/-- Every group topology on `H × F` has small invariant neighbourhoods, when `H` is abelian with
`h ^ p = 1` and `F` is finite with `(f ^ p) ^ k = f`. -/
private theorem hasSmallInvariantNhds_prod {H F : Type*} [CommGroup H] [Group F] [Finite F]
    {p k : ℕ} (hH : ∀ h : H, h ^ p = 1) (hF : ∀ f : F, (f ^ p) ^ k = f)
    (τ : GroupTopology (H × F)) : HasSmallInvariantNhds τ := by
  let := τ.toTopologicalSpace
  have := τ.toIsTopologicalGroup
  intro U hU
  -- `N` is the closure of `{1}` and `K = H × N₂`, where `N₂ = {f | (1, f) ∈ N}`.
  let N : Subgroup (H × F) := (⊥ : Subgroup (H × F)).topologicalClosure
  have hNn : N.Normal := Subgroup.is_normal_topologicalClosure ⊥
  have hNcl : (N : Set (H × F)) = closure ({1} : Set (H × F)) := by
    rw [Subgroup.topologicalClosure_coe, Subgroup.coe_bot]
  let K : Subgroup (H × F) := (N.comap (MonoidHom.inr H F)).comap (MonoidHom.snd H F)
  have hKmem : ∀ g : H × F, g ∈ K ↔ ((1 : H), g.2) ∈ N := fun g => Iff.rfl
  have hKpow : (K : Set (H × F)) = (fun g => g ^ p) ⁻¹' (N : Set (H × F)) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_preimage, hKmem]
    have hgp : g ^ p = ((1 : H), g.2) ^ p := by
      ext
      · simp [hH]
      · simp
    rw [hgp]
    refine ⟨fun h => pow_mem h p, fun h => ?_⟩
    have : ((1 : H), g.2) = (((1 : H), g.2) ^ p) ^ k := by
      ext
      · simp
      · simp [hF]
    rw [this]
    exact pow_mem h k
  have hKclosed : IsClosed (K : Set (H × F)) := by
    rw [hKpow]
    exact (Subgroup.isClosed_topologicalClosure _).preimage (continuous_pow p)
  have hKopen : IsOpen (K : Set (H × F)) := K.isOpen_of_isClosed_of_finiteIndex hKclosed
  refine ⟨interior U ∩ K, inter_mem (interior_mem_nhds.2 hU) (hKopen.mem_nhds K.one_mem),
    Set.inter_subset_left.trans interior_subset, ?_⟩
  intro g x hx
  have hxN : ((1 : H), x.2) ∈ N := hx.2
  -- `g * x * g⁻¹ = x * n` with `n ∈ {1} × N₂`, as `H` is central and `N₂` is normal.
  have hn : ((1 : H), x.2⁻¹ * g.2 * x.2 * g.2⁻¹) ∈ N := by
    have h1 : ((1 : H), g.2) * ((1 : H), x.2) * ((1 : H), g.2)⁻¹ ∈ N := hNn.conj_mem _ hxN _
    convert N.mul_mem (N.inv_mem hxN) h1 using 1
    ext <;> simp [mul_assoc]
  have hgx : g * x * g⁻¹ = x * ((1 : H), x.2⁻¹ * g.2 * x.2 * g.2⁻¹) := by
    ext
    · simp
    · simp [mul_assoc]
  rw [hgx]
  rw [← SetLike.mem_coe, hNcl] at hn
  exact mul_mem_of_mem_closure_one (isOpen_interior.inter hKopen) hx hn

/-! ### The example: the countable direct sum of copies of `ℤ/3ℤ` times the dihedral group of
order `8` -/

private theorem pow_three_eq_one (h : Multiplicative (ℕ →₀ ZMod 3)) : h ^ 3 = 1 := by
  have : (3 : ℕ) • Multiplicative.toAdd h = 0 := by
    ext n
    simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, nsmul_eq_mul]
    rw [ZMod.natCast_self, zero_mul]
  rw [← toAdd_pow] at this
  exact this

private theorem dihedralGroup_four_pow_three_pow_three (f : DihedralGroup 4) :
    (f ^ 3) ^ 3 = f := by
  have h8 : f ^ 8 = 1 := by
    have := pow_card_eq_one (x := f)
    rwa [DihedralGroup.card] at this
  rw [← pow_mul, show 3 * 3 = 8 + 1 from rfl, pow_succ, h8, one_mul]

private theorem dihedralGroup_four_isNilpotent : Group.IsNilpotent (DihedralGroup 4) :=
  IsPGroup.isNilpotent (p := 2) (IsPGroup.of_card (n := 3) (by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
    rfl))

/--
**A countable nilpotent group with modular lattice of group topologies.** It is not the case that
for every countably infinite non-abelian nilpotent group $G$ the lattice of all (not necessarily
Hausdorff) group topologies on $G$ is not modular; that is, some countably infinite non-abelian
nilpotent group has a modular lattice of group topologies.

Peng constructs (Theorem 1.1) a countably infinite non-abelian nilpotent group whose lattice of
group topologies is modular; the Kourovka Notebook (21st issue) answers 14.4(b) "No".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.4 (V. I. Arnautov); resolution: (a) V.
Arnautov and A. Topală, Bul. Acad. Ştiinţe Repub. Mold. Mat. 1998, no. 2(27), 130-131; (b) D. Peng,
On the lattice of group topologies, preprint, arXiv:2310.08269 (2023), (b) Theorem 1.1: there is a
countably infinite non-abelian nilpotent group whose lattice of all (not necessarily Hausdorff)
group topologies is modular; the Kourovka Notebook (21st issue) marks 14.4 solved: a) Yes; b) No,
there are such groups with modular L(G), https://arxiv.org/abs/2310.08269.
-/
public theorem countableNilpotentNonabelianTopologyLatticeNotModular_refuted :
    ¬ countableNilpotentNonabelianTopologyLatticeNotModular := by
  intro h
  have : Group.IsNilpotent (DihedralGroup 4) := dihedralGroup_four_isNilpotent
  refine h (Multiplicative (ℕ →₀ ZMod 3) × DihedralGroup 4)
    (inferInstanceAs (Countable ((ℕ →₀ ZMod 3) × DihedralGroup 4))) inferInstance inferInstance
    ⟨(1, DihedralGroup.r 1), (1, DihedralGroup.sr 0), fun hxy => ?_⟩
    (isModularLattice_of_forall_hasSmallInvariantNhds
      (hasSmallInvariantNhds_prod pow_three_eq_one dihedralGroup_four_pow_three_pow_three))
  have h2 := congrArg Prod.snd hxy
  simp only [Prod.mk_mul_mk, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
    DihedralGroup.sr.injEq] at h2
  exact absurd h2 (by decide)

end MathlibExt.GroupTheory.LatticeOfGroupTopologiesModularKourovka14Problem4Wanted
