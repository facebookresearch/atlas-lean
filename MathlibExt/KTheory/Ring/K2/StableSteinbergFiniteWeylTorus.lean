/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergWeyl
public import MathlibExt.KTheory.Ring.K2.StableSteinbergWeylRelations
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteSupport
public import MathlibExt.KTheory.Ring.K2.StableSteinbergCentrality

/-! # Finite-rank Weyl, torus, and central-kernel subgroups

Minimal finite-rank carriers for Milnor Section 9: the Weyl and torus closures
over index pairs below `n`, and their central-kernel intersection. This module
adds only generator membership, the torus-in-Weyl inclusion, containment in
`finiteStage`, kernel projections with centrality, and rank-zero/rank-one
degeneracy. It proves no subgroup-level matrix-image description, normality,
torus normalizer upgrade, Bruhat decomposition, kernel generation, equality
with `torusCocycleSubgroup`, or Matsumoto claim. The boundary-torus successor
inclusion is omitted: its carrier is not transitively available from the
imports below.
It also gives the finite bounded `List.ofFn` Weyl-generator representation in
exact list order, with no matrix evaluation, permutation triviality, torus
landing, or Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableSteinberg

universe u

variable {R : Type u} [Ring R]

/-- Finite Weyl subgroup: closure of all `weyl i j hij u` with `i < n` and
`j < n`. Purpose: finite-rank Weyl carrier for Milnor Section 9. Nonclaim: no
matrix-image description, normality, or Bruhat decomposition is asserted. -/
public def finiteWeylSubgroup (n : ℕ) : Subgroup (StableSteinberg R) :=
  Subgroup.closure
    { g | ∃ (i j : ℕ) (hij : i ≠ j) (u : Rˣ),
      g = weyl (R := R) i j hij u ∧ i < n ∧ j < n }

/-- Finite torus subgroup: closure of all `torus i j hij u` with `i < n` and
`j < n`. Purpose: finite-rank torus carrier for Milnor Section 9. Nonclaim: no
normality, normalizer upgrade, or equality with `torusCocycleSubgroup` is
asserted. -/
public def finiteTorusSubgroup (n : ℕ) : Subgroup (StableSteinberg R) :=
  Subgroup.closure
    { g | ∃ (i j : ℕ) (hij : i ≠ j) (u : Rˣ),
      g = torus (R := R) i j hij u ∧ i < n ∧ j < n }

/-- Finite central-kernel subgroup: elements of the finite Weyl subgroup lying
in `ker toStableE`. Purpose: finite-rank central-kernel carrier for Milnor
Section 9. Nonclaim: no containment in the finite torus subgroup, kernel
generation, or Matsumoto claim is asserted. -/
public noncomputable def finiteCentralKernelSubgroup (n : ℕ) :
    Subgroup (StableSteinberg R) :=
  MonoidHom.ker (toStableE (R := R)) ⊓ finiteWeylSubgroup (R := R) n

/-- Generator membership: each `weyl i j hij u` with `i < n` and `j < n` lies
in `finiteWeylSubgroup n`. -/
public theorem weyl_mem_finiteWeylSubgroup {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (u : Rˣ) :
    weyl (R := R) i j hij u ∈ finiteWeylSubgroup (R := R) n := by
  apply Subgroup.subset_closure
  exact ⟨i, j, hij, u, rfl, hi, hj⟩

/-- Generator membership: each `torus i j hij u` with `i < n` and `j < n` lies
in `finiteTorusSubgroup n`. -/
public theorem torus_mem_finiteTorusSubgroup {n i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) (u : Rˣ) :
    torus (R := R) i j hij u ∈ finiteTorusSubgroup (R := R) n := by
  apply Subgroup.subset_closure
  exact ⟨i, j, hij, u, rfl, hi, hj⟩

/-- The finite torus subgroup lies in the finite Weyl subgroup, since
`torus i j hij u` is the product of two Weyl generators. -/
public theorem finiteTorusSubgroup_le_finiteWeylSubgroup (n : ℕ) :
    finiteTorusSubgroup (R := R) n ≤ finiteWeylSubgroup (R := R) n := by
  rw [finiteTorusSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, j, hij, u, rfl, hi, hj⟩ := hg
  unfold torus
  exact Subgroup.mul_mem _
    (weyl_mem_finiteWeylSubgroup hi hj hij u)
    (weyl_mem_finiteWeylSubgroup hi hj hij (-1 : Rˣ))

/-- The finite Weyl subgroup lies in `finiteStage n`, since each Weyl factor
is a product of roots with both indices below `n`. -/
public theorem finiteWeylSubgroup_le_finiteStage (n : ℕ) :
    finiteWeylSubgroup (R := R) n ≤ finiteStage (R := R) n := by
  rw [finiteWeylSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, j, hij, u, rfl, hi, hj⟩ := hg
  unfold weyl
  have h1 : x (R := R) i j hij (↑u : R) ∈ finiteStage (R := R) n :=
    x_mem_finiteStage hi hj
  have h2 : x (R := R) j i hij.symm (-(↑u⁻¹ : R)) ∈ finiteStage (R := R) n :=
    x_mem_finiteStage hj hi
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1

/-- The finite torus subgroup lies in `finiteStage n`, via the finite Weyl
subgroup. -/
public theorem finiteTorusSubgroup_le_finiteStage (n : ℕ) :
    finiteTorusSubgroup (R := R) n ≤ finiteStage (R := R) n :=
  le_trans (finiteTorusSubgroup_le_finiteWeylSubgroup n)
    (finiteWeylSubgroup_le_finiteStage n)

/-- The central-kernel subgroup projects to `ker toStableE`. -/
public theorem finiteCentralKernelSubgroup_le_ker (n : ℕ) :
    finiteCentralKernelSubgroup (R := R) n ≤
      MonoidHom.ker (toStableE (R := R)) :=
  inf_le_left

/-- The central-kernel subgroup projects to the finite Weyl subgroup. -/
public theorem finiteCentralKernelSubgroup_le_finiteWeyl (n : ℕ) :
    finiteCentralKernelSubgroup (R := R) n ≤ finiteWeylSubgroup (R := R) n :=
  inf_le_right

/-- The central-kernel subgroup is contained in the center, via the accepted
kernel-centrality theorem. -/
public theorem finiteCentralKernelSubgroup_le_center (n : ℕ) :
    finiteCentralKernelSubgroup (R := R) n ≤
      Subgroup.center (StableSteinberg R) :=
  le_trans inf_le_left (ker_toStableE_le_center (R := R))

/-- No two distinct indices lie below `0`, so the rank-zero finite Weyl
subgroup is bottom. -/
public theorem finiteWeylSubgroup_zero_eq_bot :
    finiteWeylSubgroup (R := R) 0 = ⊥ :=
  le_bot_iff.mp
    (finiteStage_zero_eq_bot (R := R) ▸ finiteWeylSubgroup_le_finiteStage (R := R) 0)

/-- No two distinct indices lie below `1`, so the rank-one finite Weyl
subgroup is bottom. -/
public theorem finiteWeylSubgroup_one_eq_bot :
    finiteWeylSubgroup (R := R) 1 = ⊥ :=
  le_bot_iff.mp
    (finiteStage_one_eq_bot (R := R) ▸ finiteWeylSubgroup_le_finiteStage (R := R) 1)

/-- No two distinct indices lie below `0`, so the rank-zero finite torus
subgroup is bottom. -/
public theorem finiteTorusSubgroup_zero_eq_bot :
    finiteTorusSubgroup (R := R) 0 = ⊥ :=
  le_bot_iff.mp
    (finiteStage_zero_eq_bot (R := R) ▸ finiteTorusSubgroup_le_finiteStage (R := R) 0)

/-- No two distinct indices lie below `1`, so the rank-one finite torus
subgroup is bottom. -/
public theorem finiteTorusSubgroup_one_eq_bot :
    finiteTorusSubgroup (R := R) 1 = ⊥ :=
  le_bot_iff.mp
    (finiteStage_one_eq_bot (R := R) ▸ finiteTorusSubgroup_le_finiteStage (R := R) 1)

-- Reverse `ofFn` through `Fin.rev`; no pinned lemma supplies this.
private theorem ofFn_comp_fin_rev {α : Type u} {m : ℕ} (f : Fin m → α) :
    (List.ofFn f).reverse = List.ofFn fun k => f (Fin.rev k) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
    congr 1
    apply Fin.ext
    change m - 1 - i = m - (i + 1)
    omega

-- Mandated `ha`/`hb` names are unreferenced by the concluding equation.
set_option linter.unusedVariables false in
/-- Every element of `finiteWeylSubgroup n` is a product of bounded Weyl generators
with distinct indices, in exact list order. Purpose: finite list representation
consumed by list evaluation. Nonclaim: no matrix evaluation, permutation triviality,
torus landing, or Matsumoto claim is asserted. -/
public theorem finiteWeylSubgroup_exists_list_repr {n : ℕ} {g : StableSteinberg R}
    (hg : g ∈ finiteWeylSubgroup (R := R) n) :
    ∃ (m : ℕ) (a b : Fin m → ℕ) (ha : ∀ k, a k < n) (hb : ∀ k, b k < n)
      (hab : ∀ k, a k ≠ b k) (u : Fin m → Rˣ),
      g = (List.ofFn (fun k => weyl (R := R) (a k) (b k) (hab k) (u k))).prod := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, u, rfl, hi, hj⟩ := hx
      exact ⟨1, fun _ => i, fun _ => j, fun _ => hi, fun _ => hj, fun _ => hij,
        fun _ => u, by simp⟩
  | one =>
      exact ⟨0, fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun k => Fin.elim0 k,
        fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun k => Fin.elim0 k, by simp⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨m₁, a₁, b₁, ha₁, hb₁, hab₁, u₁, rfl⟩ := ihx
      obtain ⟨m₂, a₂, b₂, ha₂, hb₂, hab₂, u₂, rfl⟩ := ihy
      have habcat : ∀ k : Fin (m₁ + m₂), (Fin.append a₁ a₂) k ≠
          (Fin.append b₁ b₂) k := by
        intro k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Fin.append_left, Fin.append_left]
          exact hab₁ i
        · rw [Fin.append_right, Fin.append_right]
          exact hab₂ i
      refine ⟨m₁ + m₂, Fin.append a₁ a₂, Fin.append b₁ b₂, ?_, ?_, habcat,
        Fin.append u₁ u₂, ?_⟩
      · intro k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Fin.append_left]
          exact ha₁ i
        · rw [Fin.append_right]
          exact ha₂ i
      · intro k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Fin.append_left]
          exact hb₁ i
        · rw [Fin.append_right]
          exact hb₂ i
      · have hfun : Fin.append
            (fun k : Fin m₁ => weyl (R := R) (a₁ k) (b₁ k) (hab₁ k) (u₁ k))
            (fun k : Fin m₂ => weyl (R := R) (a₂ k) (b₂ k) (hab₂ k) (u₂ k))
            = fun k : Fin (m₁ + m₂) => weyl (R := R) ((Fin.append a₁ a₂) k)
              ((Fin.append b₁ b₂) k) (habcat k) ((Fin.append u₁ u₂) k) := by
          funext k
          refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;>
            simp [Fin.append_left, Fin.append_right]
        rw [← List.prod_append, ← List.ofFn_fin_append, hfun]
  | inv x _ ih =>
      obtain ⟨m, a, b, ha, hb, hab, u, rfl⟩ := ih
      refine ⟨m, fun k => a (Fin.rev k), fun k => b (Fin.rev k), fun k => ha _,
        fun k => hb _, fun k => hab _, fun k => -(u (Fin.rev k)), ?_⟩
      have h1 : ((List.ofFn fun k : Fin m => weyl (R := R) (a k) (b k) (hab k)
        (u k)).map fun x => x⁻¹).reverse = List.ofFn fun k : Fin m =>
        weyl (R := R) (a (Fin.rev k)) (b (Fin.rev k)) (hab (Fin.rev k))
        (-(u (Fin.rev k))) := by
        rw [List.map_ofFn, ofFn_comp_fin_rev]
        congr 1
        funext k
        exact (weyl_neg_eq_inv (R := R) _ _ _ _).symm
      rw [List.prod_inv_reverse, h1]

end StableSteinberg

end AlgebraicKTheory

end
