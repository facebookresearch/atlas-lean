/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular subsets of `GL(V) ∪ {0}` and subgroups (Kourovka Notebook Problem 10.48)

Kourovka Notebook, Archive of Solved Problems, Problem 10.48 (N. D. Podufalov): `R ⊆ GL(V) ∪ {0}`,
for `V` finite-dimensional over a field of prime order, is regular if `|R| = |V|`, `0, 1 ∈ R` and
`vx ≠ vy` for every non-trivial `v ∈ V` and distinct `x, y ∈ R`. The maps `τ : x ↦ x⁻¹` (`0 ↦ 0`),
`ε : x ↦ 1 - x` and `μ_g : x ↦ x g⁻¹` (`g` a non-zero element of the set) preserve regularity, and
two regular sets are equivalent if one is obtained from the other by a sequence of them. (a) Study
the equivalence classes. (b) Is every regular subset equivalent to a subgroup of `GL(V)` together
with `0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace MathlibExt.Algebra.RegularSetSubgroupEquivalenceKourovka10Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.48 (N. D.
Podufalov). UnsolvedMath record UM-00700663 (`KOU-10.48`), dataset ulamai/UnsolvedMath v1.8.0.

`V = (ZMod p)^m` with matrices acting on row vectors (`Matrix.vecMul`). Part (a) asks for a study,
not a proposition, and is not formalized. Equivalence is reachability by finitely many steps
(`Relation.ReflTransGen`); each step can be undone (`τ` and `ε` are involutions, and `μ_{g⁻¹}`
undoes `μ_g`, as `g⁻¹ = 1 · g⁻¹` lies in the transformed set).
-/

/-- A regular subset of `GL(V) ∪ {0}` for `V = (ZMod p)^m` (matrices acting on row vectors): `|R| =
|V|`, `0, 1 ∈ R`, every nonzero element of `R` is invertible, and `v x ≠ v y` for every nonzero
`v ∈ V` and distinct `x, y ∈ R`. -/
def IsRegularSet (p m : ℕ) (R : Set (Matrix (Fin m) (Fin m) (ZMod p))) : Prop :=
  R.ncard = p ^ m ∧ 0 ∈ R ∧ 1 ∈ R ∧ (∀ x ∈ R, x ≠ 0 → IsUnit x) ∧
    ∀ v : Fin m → ZMod p, v ≠ 0 → ∀ x ∈ R, ∀ y ∈ R, x ≠ y → Matrix.vecMul v x ≠ Matrix.vecMul v y

/-- One transformation step on subsets of matrices: `τ : x ↦ x⁻¹` (with `0 ↦ 0`), `ε : x ↦ 1 - x`,
or `μ_g : x ↦ x g⁻¹` for a nonzero element `g` of the set being transformed. -/
def RegularStep {p m : ℕ} (R R' : Set (Matrix (Fin m) (Fin m) (ZMod p))) : Prop :=
  R' = (fun x => x⁻¹) '' R ∨ R' = (fun x => 1 - x) '' R ∨
    ∃ g ∈ R, g ≠ 0 ∧ R' = (fun x => x * g⁻¹) '' R

/-- Kourovka 10.48(b) (N. D. Podufalov): every regular subset is equivalent, by a finite sequence of
the transformations `τ`, `ε`, `μ_g`, to `G ∪ {0}` for a subgroup `G` of `GL(V)`. -/
def regularSetEquivalentToSubgroup : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (m : ℕ) (R : Set (Matrix (Fin m) (Fin m) (ZMod p))), IsRegularSet p m R →
    ∃ G : Subgroup (GL (Fin m) (ZMod p)),
      Relation.ReflTransGen RegularStep R ((fun g : GL (Fin m) (ZMod p) => (g : Matrix _ _ _)) ''
        (G : Set (GL (Fin m) (ZMod p))) ∪ {0})

/--
Resolved false: the Kourovka Archive answers 10.48(b) "No" (Podufalov): some regular subset is not
equivalent to any subgroup of `GL(V)` together with `0`; the Archive adds that a regular set is
closed with respect to multiplication if and only if the corresponding `(γ, γ)`-transitive plane is
defined over a near-field. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 10.48 (N. D. Podufalov); resolution: N. D. Podufalov, letter of 13 February 1989,
recorded in the Kourovka Archive, Problem 10.48(b); for (a): N. D. Podufalov, Algebra and Logic 30,
no. 1 (1991), 62-69, Archive answer to (b): "No. A regular set is closed with respect to
multiplication if and only if the corresponding (γ, γ)-transitive plane is defined over a
near-field.".
-/
public theorem_wanted regularSetEquivalentToSubgroup_refuted : ¬ regularSetEquivalentToSubgroup

end MathlibExt.Algebra.RegularSetSubgroupEquivalenceKourovka10Problem48Wanted
