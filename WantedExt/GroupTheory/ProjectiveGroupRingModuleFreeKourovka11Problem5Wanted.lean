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

/-- **Polycyclic group.** A group $G$ is polycyclic if for some $n \ge 0$ there are subgroups
$1 = H_0 \le H_1 \le \cdots \le H_n = G$ such that for each $i < n$, $H_i$ is normal in
$H_{i+1}$ and the quotient $H_{i+1} / H_i$ is cyclic. -/
def IsPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsCyclic (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))

/-- **Almost polycyclic group.** A group $G$ is almost polycyclic (polycyclic-by-finite) if it
has a subgroup of finite index that is polycyclic. -/
def IsAlmostPolycyclic (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

/-- **Artamonov's freeness question (Kourovka 11.5).** This is the proposition that, for every
commutative ring $k$, every torsion-free almost polycyclic group $G$ (no element $g \ne 1$ of $G$
has finite order) and every finitely generated projective module $P$ over the group ring $kG$, if
$P$ contains two elements that are linearly independent over $kG$, then $P$ is a free
$kG$-module. -/
def projectiveWithTwoIndependentFree : Prop :=
  ∀ (k : Type) [CommRing k] (G : Type) [Group G], (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) →
    IsAlmostPolycyclic G → ∀ (P : Type) [AddCommGroup P] [Module (MonoidAlgebra k G) P],
    Module.Finite (MonoidAlgebra k G) P → Module.Projective (MonoidAlgebra k G) P →
    (∃ x y : P, LinearIndependent (MonoidAlgebra k G) ![x, y]) →
    Module.Free (MonoidAlgebra k G) P

/--
**Artamonov's freeness question has a negative answer.** It is not the case that for every
commutative ring $k$, every torsion-free almost polycyclic group $G$ (no element $g \ne 1$ of $G$
has finite order) and every finitely generated projective module $P$ over the group ring $kG$
containing two elements that are linearly independent over $kG$, the module $P$ is free over $kG$.

Jayadevan's counterexample takes $k = \mathbb{F}_2 \times \mathbb{F}_2$ and the trivial group $G$,
so that $kG = k$; then $P = k^2 \oplus (\mathbb{F}_2 \times 0)$ is a finitely generated projective
$k$-module containing an independent pair, but $|P| = 32$ is not a power of $4 = |k|$, so $P$ is
not free. The Kourovka Notebook (21st issue) marks 11.5 solved, "No, not always" (AI solution
confirmed by D. Segal); the example gives nothing for field coefficients.

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
