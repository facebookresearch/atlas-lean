/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Point stabilizers acting regularly on a suborbit (Kourovka Notebook Problem 9.69)

Kourovka Notebook, Problem 9.69 (A. N. Fomin (after P. Cameron)), marked solved in the 21st issue:
let `G` be a finite primitive permutation group and suppose that the stabilizer `G_α` of a point `α`
induces on some of its orbits `Δ ≠ {α}` a regular permutation group. Is it true that `|G_α| = |Δ|`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.GroupAction.Primitive

@[expose] public section

namespace MathlibExt.GroupTheory.RegularSuborbitStabilizerOrderKourovka9Problem69Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 9.69 (A. N. Fomin). UnsolvedMath record
UM-00700602 (`KOU-9.69`), dataset ulamai/UnsolvedMath v1.8.0.

A finite primitive permutation group is a subgroup `G` of `Equiv.Perm Ω`, `Ω` finite, acting
primitively (Mathlib's `MulAction.IsPreprimitive`, which includes transitivity). `Δ` is the
`G_α`-orbit of a point `δ ≠ α` (so `Δ ≠ {α}`). The induced group on `Δ` is transitive, and it is
regular when it is semiregular: two elements of `G_α` that agree at `δ` agree on all of `Δ`. Then
`|G_α| = |Δ|` says that `G_α` acts faithfully on `Δ`.
-/

/-- Kourovka 9.69 (A. N. Fomin, after P. Cameron): let `G ≤ Sym(Ω)` be a finite primitive
permutation group, `α ∈ Ω`, and `Δ = G_α • δ` an orbit of the point stabilizer `G_α` with `δ ≠ α`
on which `G_α` induces a regular permutation group (elements of `G_α` that agree at `δ` agree on all
of `Δ`). Then `|G_α| = |Δ|`. -/
def regularSuborbitStabilizerOrder : Prop :=
  ∀ (Ω : Type) [Finite Ω] (G : Subgroup (Equiv.Perm Ω)), MulAction.IsPreprimitive G Ω →
    ∀ α δ : Ω, δ ≠ α →
      (∀ g ∈ MulAction.stabilizer G α, ∀ h ∈ MulAction.stabilizer G α, g • δ = h • δ →
        ∀ ω ∈ MulAction.orbit (MulAction.stabilizer G α) δ, g • ω = h • ω) →
      Nat.card (MulAction.stabilizer G α) = Nat.card (MulAction.orbit (MulAction.stabilizer G α) δ)

/--
Resolved false: Spiga constructs a finite primitive group `G` (of diagonal type) and points `α ≠ β`
with `G_αβ` normal in `G_α` and `G_αβ ≠ 1`, so `G_α` induces a regular group on the suborbit
`β^{G_α}` while `|G_α| > |β^{G_α}|`; the Kourovka Notebook (21st issue) marks 9.69 solved: "No, not
always". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 9.69 (A. N. Fomin); resolution: P.
Spiga, A generalization of Sims' conjecture for finite primitive groups and two point stabilizers in
primitive groups, J. Group Theory 25 (2022), no. 1, 113-126, abstract and Section 1
(arXiv:2102.13614): a finite primitive group G on Ω and distinct points α, β with G_αβ normal in G_α
and G_αβ ≠ 1, answering the question of Cameron and of Fomin (Kourovka 9.69); the Kourovka Notebook
(21st issue) marks 9.69 solved: "No, not always", https://doi.org/10.1515/jgth-2021-0032.
-/
public theorem_wanted regularSuborbitStabilizerOrder_refuted : ¬ regularSuborbitStabilizerOrder

end MathlibExt.GroupTheory.RegularSuborbitStabilizerOrderKourovka9Problem69Wanted
