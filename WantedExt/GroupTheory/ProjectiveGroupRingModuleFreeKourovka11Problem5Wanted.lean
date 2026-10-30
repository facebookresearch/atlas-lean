/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Projective modules over group rings of polycyclic groups (Kourovka Notebook Problem 11.5)

Kourovka Notebook, Problem 11.5 (V. A. Artamonov): let `k` be a commutative ring and `G` a
torsion-free almost polycyclic group. If `P` is a finitely generated projective `kG`-module
containing two elements independent over `kG`, is `P` free?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.5 (V. A. Artamonov). UnsolvedMath record
UM-00700698 (`KOU-11.5`), dataset ulamai/UnsolvedMath v1.8.0.

The statement is the literal one, over an arbitrary commutative ring `k`, which is what the Notebook
asks and what its accepted answer refutes. Almost polycyclic means polycyclic-by-finite (a
polycyclic subgroup of finite index); torsion-free means no nontrivial element of finite order. The
group ring `kG` is `MonoidAlgebra k G`, and two independent elements are a `kG`-linearly independent
pair. The refutation uses a coefficient ring that is not a field, `𝔽₂ × 𝔽₂` (it has nontrivial
idempotents), and the trivial group; the question for field coefficients is not settled by it.
-/

/-- `G` is polycyclic: it has a finite subnormal series `1 = H₀ ≤ H₁ ≤ ⋯ ≤ Hₙ = G`, each `Hᵢ`
normal in `Hᵢ₊₁`, with cyclic factors `Hᵢ₊₁ / Hᵢ`. -/
def IsPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsCyclic (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))

/-- `G` is almost polycyclic (polycyclic-by-finite): some subgroup of finite index is
polycyclic. -/
def IsAlmostPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

/-- Kourovka 11.5 (V. A. Artamonov): if `k` is a commutative ring, `G` a torsion-free almost
polycyclic group and `P` a finitely generated projective `kG`-module containing two elements that
are linearly independent over `kG`, then `P` is a free `kG`-module. -/
def projectiveWithTwoIndependentFree : Prop :=
  ∀ (k : Type) [CommRing k] (G : Type) [Group G], (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    IsAlmostPolycyclic G → ∀ (P : Type) [AddCommGroup P] [Module (MonoidAlgebra k G) P],
    Module.Finite (MonoidAlgebra k G) P → Module.Projective (MonoidAlgebra k G) P →
    (∃ x y : P, LinearIndependent (MonoidAlgebra k G) ![x, y]) →
    Module.Free (MonoidAlgebra k G) P

/--
Resolved false for the literal statement, with a coefficient ring that is not a field: Jayadevan
takes `k = 𝔽₂ × 𝔽₂` and the trivial group `G` (so `kG = k`); `P = k² ⊕ (𝔽₂ × 0)` is a finitely
generated projective `k`-module containing an independent pair, but `|P| = 32` is not a power of
`4 = |k|`, so `P` is not free. The Kourovka Notebook (21st issue) marks 11.5 solved, "No, not
always" (AI solution confirmed by D. Segal); the example gives nothing for field coefficients.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.5 (V. A. Artamonov); resolution: A.
Jayadevan, A coefficient-ring obstruction to freeness of projective group-ring modules, preprint,
Zenodo record 22846603 (2026), main example: `k = 𝔽₂ × 𝔽₂`, `G = 1`, `P = k² ⊕ (𝔽₂ × 0)` is
projective with an independent pair but has 32 elements, while finite free `k`-modules have `4ⁿ`;
the Kourovka Notebook (21st issue) marks 11.5 solved (AI solution confirmed by D. Segal),
https://zenodo.org/records/22846603.
-/
public theorem_wanted projectiveWithTwoIndependentFree_refuted : ¬ projectiveWithTwoIndependentFree

end MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted
