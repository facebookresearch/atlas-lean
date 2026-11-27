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
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A counterexample to Artamonov's freeness question

For a commutative ring $k$ and a torsion-free almost polycyclic group $G$, a finitely generated
projective $kG$-module with two $kG$-linearly independent elements need not be free. Take
$G = 1$, $k = \mathbb{F}_2 \times \mathbb{F}_2$, and $k^2 \oplus (\mathbb{F}_2 \times 0)$.
This does not settle the question for field coefficients.

## References

* E. I. Khukhro and V. D. Mazurov (eds.), *Unsolved Problems in Group Theory: The Kourovka
  Notebook*, 21st issue, Novosibirsk (2026), Problem 11.5 (V. A. Artamonov), p. 48,
  arXiv:1401.0300v49.
* Achyuth Jayadevan, *A coefficient-ring obstruction to freeness of projective group-ring
  modules*, preprint (2026), main counterexample, https://doi.org/10.5281/zenodo.22846603.
-/

set_option autoImplicit false

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
  let F := ZMod 2
  let k := F × F
  let R := MonoidAlgebra k PUnit
  let e : R ≃+* k := MonoidAlgebra.uniqueRingEquiv PUnit
  have htf (g : PUnit) (hg : g ≠ 1) : ¬ IsOfFinOrder g := (hg (Subsingleton.elim _ _)).elim
  have hpc : IsAlmostPolycyclic PUnit := by
    refine ⟨⊤, inferInstance, 0, fun _ => ⊤, Subsingleton.elim _ _, rfl, Fin.elim0⟩
  let _ : Module R F := Module.compHom F ((RingHom.fst F F).comp e.toRingHom)
  let P := (Fin 2 → R) × F
  -- The first factor of the coefficient ring is a direct summand over the group ring.
  let s : F →ₗ[R] R :=
    { toFun := fun x => e.symm (x, 0)
      map_add' := fun x y => e.injective (by
        rw [map_add, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
        change (x + y, (0 : F)) = (x + y, 0 + 0)
        rw [zero_add])
      map_smul' := fun r x => e.injective (by
        change e (e.symm ((e r).1 * x, 0)) = e (r * e.symm (x, 0))
        rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
        change ((e r).1 * x, 0) = ((e r).1 * x, (e r).2 * 0)
        rw [mul_zero]) }
  let i : P →ₗ[R] (Fin 2 → R) × R := LinearMap.id.prodMap s
  let p : ((Fin 2 → R) × R) →ₗ[R] P :=
    LinearMap.id.prodMap (LinearMap.toSpanSingleton R F 1)
  have hsplit : p.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (x.1, (e (e.symm (x.2, 0))).1 * 1) = x
    simp
  have hproj : Module.Projective R P := Module.Projective.of_split i p hsplit
  have : Finite R := Finite.of_equiv k e.symm.toEquiv
  have hfin : Module.Finite R P := Module.Finite.of_finite
  have hli : ∃ x y : P, LinearIndependent R ![x, y] := by
    let b := Pi.basisFun R (Fin 2)
    let j : (Fin 2 → R) →ₗ[R] P := LinearMap.inl R (Fin 2 → R) F
    refine ⟨j (b 0), j (b 1), ?_⟩
    have hv : ![j (b 0), j (b 1)] = j ∘ b := by
      funext a
      fin_cases a <;> rfl
    rw [hv]
    exact b.linearIndependent.map' j (LinearMap.ker_eq_bot.mpr (LinearMap.inl_injective ..))
  have : Module.Free R P := h k PUnit htf hpc P hfin hproj hli
  have hF : Nat.card F = 2 := by simp [F, Nat.card_eq_fintype_card, ZMod.card]
  have hR : Nat.card R = 4 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hF]
  have hP : Nat.card P = 32 := by
    change Nat.card ((Fin 2 → R) × F) = 32
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, hR, hF]
    decide
  let b := Module.Free.chooseBasis R P
  have : Finite (Module.Free.ChooseBasisIndex R P) := Finite.of_injective b b.injective
  have hpow : 4 ^ Nat.card (Module.Free.ChooseBasisIndex R P) = 32 := by
    rw [← hP, Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, hR]
  have hexp := Nat.pow_right_injective (show 2 ≤ 2 by rfl)
    (show 2 ^ (2 * Nat.card (Module.Free.ChooseBasisIndex R P)) = 2 ^ 5 by
      rw [pow_mul]
      exact hpow)
  omega

end MathlibExt.GroupTheory.ProjectiveGroupRingModuleFreeKourovka11Problem5Wanted
