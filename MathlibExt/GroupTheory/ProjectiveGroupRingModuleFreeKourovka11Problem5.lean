/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Finiteness.Defs
public import MathlibExt.GroupTheory.GroupClassesShared
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Artamonov's freeness question for projective modules over group rings

The group ring of the trivial group over `𝔽₂ × 𝔽₂` has a finite projective module with an
independent pair and 32 elements. Its cardinality rules out a basis, refuting the assertion in
Kourovka Notebook Problem 11.5.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.5 (V. A. Artamonov). UnsolvedMath record
UM-00700698 (`KOU-11.5`), dataset ulamai/UnsolvedMath v1.8.0.

The statement is the literal one, over an arbitrary commutative ring `k`, which is what the Notebook
asks and what its accepted answer refutes. Almost polycyclic means polycyclic-by-finite (a
polycyclic subgroup of finite index; `IsAlmostPolycyclic` of `GroupClassesShared`); torsion-free
means no nontrivial element of finite order. The group ring `kG` is `MonoidAlgebra k G`, and two
independent elements are a `kG`-linearly independent pair. The refutation uses a coefficient ring
that is not a field, `𝔽₂ × 𝔽₂` (it has nontrivial idempotents), and the trivial group; the question
for field coefficients is not settled by it.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted

open MathlibExt.GroupTheory.GroupClassesShared (IsAlmostPolycyclic)

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

private lemma trivial_almostPolycyclic : IsAlmostPolycyclic Unit := by
  refine ⟨⊤, inferInstance, 0, fun _ ↦ ⊥, rfl, Subsingleton.elim _ _, ?_⟩
  exact Fin.elim0

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
theorem projectiveWithTwoIndependentFree_refuted : ¬ projectiveWithTwoIndependentFree := by
  classical
  intro h
  let k := ZMod 2 × ZMod 2
  let R := MonoidAlgebra k Unit
  let e : R ≃+* k := MonoidAlgebra.uniqueRingEquiv Unit
  let proj : R →+* ZMod 2 := (RingHom.fst _ _).comp e.toRingHom
  let : Module R (ZMod 2) := Module.compHom _ proj
  -- The first coordinate is a direct summand via the section x ↦ (x, 0).
  let incl : ZMod 2 →ₗ[R] R :=
    { toFun x := e.symm (x, 0)
      map_add' x y := by rw [← map_add]; congr 1
      map_smul' r x := by
        apply e.injective
        change e (e.symm ((e r).1 * x, 0)) = e (r * e.symm (x, 0))
        rw [e.apply_symm_apply, map_mul, e.apply_symm_apply]
        exact Prod.ext rfl (mul_zero _).symm }
  have : Module.Projective R (ZMod 2) :=
    Module.Projective.of_split incl (Module.compHom.toLinearMap proj) (by
      apply LinearMap.ext
      intro x
      change (e (e.symm (x, 0))).1 = x
      simp)
  let P := (R × R) × ZMod 2
  let : Fintype R := Fintype.ofEquiv k e.symm.toEquiv
  have hpair : ∃ x y : P, LinearIndependent R ![x, y] := by
    refine ⟨((1, 0), 0), ((0, 1), 0), LinearIndependent.pair_iff.mpr ?_⟩
    intro a b hab
    have hcoords := congrArg Prod.fst hab
    change (a * 1 + b * 0, a * 0 + b * 1) = (0, 0) at hcoords
    simpa using hcoords
  have : Module.Free R P :=
    h k Unit (fun g hg ↦ (hg (Subsingleton.elim _ _)).elim) trivial_almostPolycyclic
      P inferInstance inferInstance hpair
  have hR : Fintype.card R = 4 := by
    rw [Fintype.card_congr e.toEquiv]
    simp [k]
  -- A basis of size n would give 2 ^ 5 = 2 ^ (2 * n).
  have hc := Module.card_fintype (Module.Free.chooseBasis R P)
  rw [show Fintype.card P = 32 by simp [P, Fintype.card_prod, hR, ZMod.card], hR] at hc
  let n := Fintype.card (Module.Free.ChooseBasisIndex R P)
  change 2 ^ 5 = (2 ^ 2) ^ n at hc
  rw [← pow_mul, Nat.pow_right_inj (by decide : 1 < 2)] at hc
  omega

end MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted
