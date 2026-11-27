/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

import Mathlib.Data.Int.ModEq
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Logic.Equiv.Nat
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.Separation.DisjointCover

/-!
# Subgroups of `ℤ^ω` with free dual of uncountable rank (Kourovka Notebook Problem 17.24)

Kourovka Notebook, Archive of Solved Problems, Problem 17.24 (G. M. Bergman): (A. Blass, J. Irwin,
G. Schlitt). Does `ℤ^ω` have a subgroup whose dual is free of uncountable rank?

We prove that a subgroup of the Baer–Specker group has free dual of uncountable rank.
Inspired by the group topologies on `ℤ` in §6 of Bergman's *More Abelian groups with free duals*,
we use functions on Cantor space with values in the integers with their 2-adic topology.
Restriction to a countable dense set embeds this group in `ℤ^ω`, and the point evaluations form
a basis of its dual.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.24 (G. M.
Bergman). UnsolvedMath record UM-00701326 (`KOU-17.24`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤ^ω` is `ℕ → ℤ`, the dual of `H` is `Hom(H, ℤ) = H →+ ℤ` as a `ℤ`-module, free means `Module.Free
ℤ`, and uncountable rank means `ℵ₀ < Module.rank`.
-/

namespace MathlibExt.GroupTheory.BaerSpeckerSubgroupDualFreeKourovka17Problem24Wanted

/-- **Bergman's question on subgroups of the Baer–Specker group (Kourovka 17.24).** The
proposition that the Baer–Specker group $\mathbb{Z}^{\mathbb{N}}$ of all integer sequences has a
subgroup $H$ whose dual $\operatorname{Hom}(H, \mathbb{Z})$ is a free abelian group of rank
greater than $\aleph_0$. -/
@[expose] public def baerSpeckerSubgroupDualFreeUncountable : Prop :=
  ∃ H : AddSubgroup (ℕ → ℤ), Module.Free ℤ (H →+ ℤ) ∧ Cardinal.aleph0 < Module.rank ℤ (H →+ ℤ)

noncomputable section

open Filter Set Topology

private abbrev X := ℕ → Bool

-- Integer-valued functions continuous for the 2-adic topology on the codomain.
private def functions : AddSubgroup (X → ℤ) where
  carrier := {f | ∀ (k : ℕ) (x : X), ∀ᶠ y in 𝓝 x, f y ≡ f x [ZMOD 2 ^ k]}
  zero_mem' := fun _ _ ↦ .of_forall fun _ ↦ .rfl
  add_mem' := by
    intro f g hf hg k x
    filter_upwards [hf k x, hg k x] with y hy hy' using hy.add hy'
  neg_mem' := by
    intro f hf k x
    filter_upwards [hf k x] with y hy using hy.neg

private abbrev G := ↥functions

private theorem residues (f : G) (k : ℕ) (x : X) :
    ∀ᶠ y in 𝓝 x, f.val y ≡ f.val x [ZMOD 2 ^ k] := f.property k x

-- Pointwise divisibility by a power of two is divisibility in the subgroup.
private theorem map_congr (φ : G →+ ℤ) (k : ℕ) {f g : G}
    (h : ∀ x, f.val x ≡ g.val x [ZMOD 2 ^ k]) : φ f ≡ φ g [ZMOD 2 ^ k] := by
  choose q hq using fun x ↦ (h x).dvd
  have hmem : q ∈ functions := by
    intro j x
    filter_upwards [residues g (k + j) x, residues f (k + j) x] with y hg hf
    have hdiff := hg.sub hf
    rw [hq x, hq y, pow_add] at hdiff
    exact Int.ModEq.mul_left_cancel' (by positivity) hdiff
  have heq : g - f = (2 ^ k : ℤ) • (⟨q, hmem⟩ : G) := Subtype.ext (funext hq)
  exact Int.modEq_of_dvd ⟨φ ⟨q, hmem⟩, by simpa using congrArg φ heq⟩

private theorem eq_of_congr (a b : ℤ) (h : ∀ k : ℕ, a ≡ b [ZMOD 2 ^ k]) :
    a = b := by
  by_contra hne
  let n := (b - a).natAbs
  have hle := Int.natAbs_le_of_dvd_ne_zero (h n).dvd (sub_ne_zero.mpr (Ne.symm hne))
  have : 2 ^ n ≤ n := by simpa [Int.natAbs_pow, n] using hle
  exact (Nat.not_le_of_lt Nat.lt_two_pow_self) this

private def constant (z : ℤ) : G := ⟨fun _ ↦ z, fun _ _ ↦ .of_forall fun _ ↦ .rfl⟩

private def cut (U : Set X) (hU : IsClopen U) (f : G) : G := by
  classical
  refine ⟨U.indicator f.val, ?_⟩
  intro k x
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx, residues f k x] with y hy h
    simpa [Set.indicator_of_mem, hx, hy] using h
  · filter_upwards [hU.compl.isOpen.mem_nhds (show x ∈ Uᶜ from hx)] with y hy
    simp [Set.indicator_of_notMem, hx, show y ∉ U from hy]

private def cylinder (x : X) (n : ℕ) : Set X := {y | ∀ i < n, y i = x i}

private theorem clopen_cylinder (x : X) (n : ℕ) : IsClopen (cylinder x n) := by
  have heq : cylinder x n = ⋂ i ∈ Finset.range n, (fun y : X ↦ y i) ⁻¹' {x i} := by
    ext y
    simp [cylinder]
  rw [heq]
  exact isClopen_biInter_finset fun i _ ↦ (isClopen_discrete {x i}).preimage (continuous_apply i)

-- A homomorphism cannot detect every term of a pointwise eventually zero sequence.
-- Build a function whose image would differ from the nth integer modulo an increasing
-- power of two at stage n. At each point only finitely many corrections are made.
private theorem some_in_kernel (φ : G →+ ℤ) (u : ℕ → G)
    (hu : ∀ x, ∃ N, ∀ n ≥ N, (u n).val x = 0) : ∃ n, φ (u n) = 0 := by
  classical
  by_contra! hnon
  let e := Equiv.intEquivNat.symm
  have step (n : ℕ) (s : G × ℕ) : ∃ t : G × ℕ, s.2 < t.2 ∧
      (∀ x, s.1.val x ≡ t.1.val x [ZMOD 2 ^ s.2]) ∧
      (∀ x, (u n).val x = 0 → t.1.val x = s.1.val x) ∧
      ¬ φ t.1 ≡ e n [ZMOD 2 ^ t.2] := by
    let c : ℤ := if φ s.1 = e n then 2 ^ s.2 else 0
    let v := s.1 + c • u n
    have hv : φ v ≠ e n := by
      by_cases he : φ s.1 = e n
      · simpa [v, c, he, zsmul_eq_mul] using hnon n
      · simp [v, c, he]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, ¬ φ v ≡ e n [ZMOD 2 ^ j] := by
      by_contra! h
      exact hv (eq_of_congr _ _ h)
    refine ⟨(v, max (s.2 + 1) j), by simp, ?_, ?_, ?_⟩
    · intro x
      apply Int.modEq_of_dvd
      change 2 ^ s.2 ∣ s.1.val x + c * (u n).val x - s.1.val x
      simp only [add_sub_cancel_left]
      apply dvd_mul_of_dvd_left _ _
      simp [c, apply_ite]
    · intro x hx
      change s.1.val x + c * (u n).val x = s.1.val x
      simp [hx]
    · exact fun h ↦ hj (h.of_dvd (pow_dvd_pow _ (le_max_right _ _)))
  -- Later corrections preserve all residues already used to exclude an integer.
  choose next inc congr stable avoid using step
  let S : ℕ → G × ℕ := Nat.rec (0, 0) next
  have hinc : StrictMono fun n ↦ (S n).2 := strictMono_nat_of_lt_succ fun n ↦ inc n (S n)
  have hcong (i j : ℕ) (hij : i ≤ j) (x : X) :
      (S i).1.val x ≡ (S j).1.val x [ZMOD 2 ^ (S i).2] := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hij ih =>
      exact ih.trans ((congr j (S j) x).of_dvd (pow_dvd_pow _ (hinc.monotone hij)))
  -- The pointwise limit takes integer values, and each of its residues is locally constant.
  choose N hN using hu
  let g (x : X) := (S (N x)).1.val x
  have hstable (x : X) (j : ℕ) (hj : N x ≤ j) : (S j).1.val x = g x := by
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => exact (stable j (S j) x (hN x j hj)).trans ih
  have hlim (i : ℕ) (x : X) : (S i).1.val x ≡ g x [ZMOD 2 ^ (S i).2] :=
    hstable x _ (le_max_right i (N x)) ▸ hcong i _ (le_max_left i (N x)) x
  have hg : g ∈ functions := by
    intro k x
    have hd := pow_dvd_pow (2 : ℤ) (hinc.id_le k)
    filter_upwards [residues (S k).1 k x] with y hy
    exact ((hlim k y).of_dvd hd).symm.trans (hy.trans ((hlim k x).of_dvd hd))
  let z : G := ⟨g, hg⟩
  obtain ⟨n, hn⟩ := e.surjective (φ z)
  exact avoid n (S n) (hn.symm ▸ map_congr φ _ (g := z) (hlim (n + 1)))

-- On a sufficiently small cylinder about x, only the value at x matters to φ.
private theorem local_kernel (φ : G →+ ℤ) (x : X) :
    ∃ n, ∀ f : G, (∀ y ∉ cylinder x n, f.val y = 0) → f.val x = 0 → φ f = 0 := by
  by_contra! h
  choose u hU hx hnon using h
  apply (some_in_kernel φ u _).elim fun n hn ↦ hnon n hn
  intro y
  by_cases hy : y = x
  · subst y
    exact ⟨0, fun n _ ↦ hx n⟩
  · obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := Function.ne_iff.mp hy
    exact ⟨i + 1, fun n hn ↦ hU n y fun hmem ↦ hi (hmem i (by omega))⟩

private def evaluation (x : X) : G →+ ℤ where
  toFun f := f.val x
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem evaluations_span :
    ⊤ ≤ Submodule.span ℤ (Set.range evaluation) := by
  classical
  intro φ _
  choose depth hdepth using local_kernel φ
  let U (x : X) : TopologicalSpace.Opens X :=
    ⟨cylinder x (depth x), (clopen_cylinder _ _).isOpen⟩
  have hcover : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    exact ⟨x, fun _ _ ↦ rfl⟩
  -- A finite clopen partition lets us add the local formulas without double counting.
  obtain ⟨n, W, hW, hcov, hdis⟩ := hcover.exists_finite_nonempty_disjoint_clopen_cover
  choose point hsub using fun i ↦ (hW i).2
  let piece (i : Fin n) := cut (W i) (W i).isClopen
  let weight (i : Fin n) := φ (piece i (constant 1))
  have hp (f : G) (i : Fin n) : φ (piece i f) = weight i * f.val (point i) := by
    let z := f.val (point i)
    have he : φ (piece i f - z • piece i (constant 1)) = 0 := by
      apply hdepth (point i)
      · intro y hy
        have hy' : y ∉ W i := fun h ↦ hy (hsub i h)
        change (W i : Set X).indicator f.val y -
          z * (W i : Set X).indicator (fun _ ↦ (1 : ℤ)) y = 0
        simp [hy']
      · change (W i : Set X).indicator f.val (point i) -
          z * (W i : Set X).indicator (fun _ ↦ (1 : ℤ)) (point i) = 0
        by_cases h : point i ∈ W i <;> simp [h, z]
    simpa [map_sub, map_zsmul, sub_eq_zero, weight, z, mul_comm, zsmul_eq_mul] using he
  have hsum (f : G) : ∑ i, piece i f = f := by
    apply Subtype.ext
    funext x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
    change (evaluation x) (∑ i, piece i f) = f.val x
    rw [map_sum, Fintype.sum_eq_single j]
    · exact Set.indicator_of_mem hj _
    · intro i hi
      have hd := TopologicalSpace.Clopens.coe_disjoint.mpr (hdis hi)
      exact Set.indicator_of_notMem (fun hx ↦ Set.disjoint_left.mp hd hx hj) _
  have he : φ = ∑ i, weight i • evaluation (point i) := by
    ext f
    calc
      φ f = ∑ i, φ (piece i f) := by rw [← map_sum, hsum]
      _ = _ := by
        change _ = AddMonoidHom.eval f (∑ i, weight i • evaluation (point i))
        rw [map_sum]
        simp [hp, evaluation]
  rw [he]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self _))

private theorem evaluations_independent : LinearIndependent ℤ evaluation := by
  classical
  refine linearIndependent_iff'.mpr fun s c h x hx ↦ ?_
  let t := s.erase x
  obtain ⟨V, hV, hxV, hVt⟩ := exists_isClopen_mem_of_isOpen
    t.finite_toSet.isClosed.isOpen_compl (show x ∈ (t : Set X)ᶜ by simp [t])
  let f := cut V hV (constant 1)
  have hsum := congrArg (AddMonoidHom.eval f) h
  simp only [map_sum, map_zero, map_zsmul] at hsum
  rw [Finset.sum_eq_single_of_mem x hx] at hsum
  · simpa [evaluation, f, cut, constant, hxV] using hsum
  · intro y hy hyx
    have hyV : y ∉ V := fun hy' ↦ hVt hy' (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    simp [evaluation, f, cut, hyV]

private def restriction : G →+ (ℕ → ℤ) where
  toFun f n := f.val (TopologicalSpace.denseSeq X n)
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem restriction_injective : Function.Injective restriction := by
  intro f g h
  apply Subtype.ext
  funext x
  apply eq_of_congr
  intro k
  obtain ⟨_, ⟨n, rfl⟩, hf, hg⟩ := (TopologicalSpace.denseRange_denseSeq X).inter_nhds_nonempty
    ((residues f k x).and (residues g k x))
  have he : f.val (TopologicalSpace.denseSeq X n) = g.val (TopologicalSpace.denseSeq X n) :=
    congrFun h n
  exact hf.symm.trans (he.symm ▸ hg)

/--
**A subgroup of the Baer–Specker group with free dual of uncountable rank.** The Baer–Specker
group $\mathbb{Z}^{\mathbb{N}}$ of all integer sequences has a subgroup $H$ whose dual
$\operatorname{Hom}(H, \mathbb{Z})$ is a free abelian group of rank greater than $\aleph_0$; this
answers Kourovka 17.24 positively.

Bergman's subgroup has dual free abelian of rank $2^{\aleph_0}$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.24 (G. M.
Bergman); resolution: G. M. Bergman, More Abelian groups with free duals, Portugaliae Math. 69
(2012), 69-84 (arXiv:1104.3827), abstract (a subgroup of ℤ^ω whose dual Hom(G, ℤ) is free abelian of
rank 2^ℵ₀); Kourovka Archive, Problem 17.24 (Yes, it does), https://arxiv.org/abs/1104.3827.
-/
public theorem baerSpeckerSubgroupDualFreeUncountable_holds :
    baerSpeckerSubgroupDualFreeUncountable := by
  let e : G ≃+ restriction.range := AddMonoidHom.ofInjective restriction_injective
  let b := Module.Basis.mk evaluations_independent evaluations_span
  let basis := b.map (e.addMonoidHomCongrLeft (N := ℤ)).toIntLinearEquiv
  refine ⟨restriction.range, Module.Free.of_basis basis, ?_⟩
  rw [← basis.mk_eq_rank'']
  change Cardinal.aleph0 < Cardinal.mk (ℕ → Bool)
  rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id]
  exact Cardinal.aleph0_lt_continuum

end

end MathlibExt.GroupTheory.BaerSpeckerSubgroupDualFreeKourovka17Problem24Wanted
