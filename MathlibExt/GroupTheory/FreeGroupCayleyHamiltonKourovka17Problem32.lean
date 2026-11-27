/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# A counterexample to Bogopolski's Cayley–Hamilton analogue for free groups

The theorem `freeGroupCayleyHamilton_refuted` formalizes the rank-two counterexample
of Ionin and Semidetnov to Problem 17.32 of the Kourovka Notebook.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.32 (O. V. Bogopolski). UnsolvedMath
record UM-00701334 (`KOU-17.32`), dataset ulamai/UnsolvedMath v1.8.0.

`Fₙ = FreeGroup (Fin n)`, `Aut(Fₙ) = MulAut (FreeGroup (Fin n))` and `φⁱ` is the `i`-th power in
`MulAut`; the question quantifies over all `n`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupCayleyHamiltonKourovka17Problem32Wanted

/-- **Bogopolski's Cayley–Hamilton question for free groups (Kourovka 17.32).** The assertion
that for every natural number $n$, every element $w$ of the free group $F_n$ of rank $n$ and every
automorphism $\varphi$ of $F_n$, if $w, \varphi(w), \dots, \varphi^n(w)$ generate $F_n$, then
already $w, \varphi(w), \dots, \varphi^{n-1}(w)$ generate $F_n$. -/
def freeGroupCayleyHamilton : Prop :=
  ∀ (n : ℕ) (w : FreeGroup (Fin n)) (φ : MulAut (FreeGroup (Fin n))),
    Subgroup.closure {x | ∃ i ≤ n, x = (φ ^ i) w} = ⊤ →
      Subgroup.closure {x | ∃ i < n, x = (φ ^ i) w} = ⊤

private abbrev x : FreeGroup (Fin 2) := FreeGroup.of 0
private abbrev y : FreeGroup (Fin 2) := FreeGroup.of 1

/-- The substitution `x ↦ yx`, `y ↦ x` has inverse `x ↦ y`, `y ↦ xy⁻¹`. -/
private def φ : MulAut (FreeGroup (Fin 2)) :=
  let f := FreeGroup.lift fun i : Fin 2 => if i = 0 then y * x else x
  let g := FreeGroup.lift fun i : Fin 2 => if i = 0 then y else x * y⁻¹
  f.toMulEquiv g
    (FreeGroup.ext_hom _ _ (Fin.forall_fin_two.mpr (by simp [f, g, x, y])))
    (FreeGroup.ext_hom _ _ (Fin.forall_fin_two.mpr (by simp [f, g, x, y])))

private theorem φ_x : φ x = y * x := by
  simp [φ, x, MonoidHom.toMulEquiv_apply]

private theorem φ_y : φ y = x := by
  simp [φ, y, MonoidHom.toMulEquiv_apply]

private theorem three_generate :
    Subgroup.closure {z | ∃ i ≤ 2, z = (φ ^ i) (x * y)} = ⊤ := by
  let H := Subgroup.closure {z | ∃ i ≤ 2, z = (φ ^ i) (x * y)}
  have hw : x * y ∈ H := Subgroup.subset_closure ⟨0, by decide, by simp⟩
  have h₂ : (φ ^ 2) (x * y) ∈ H := Subgroup.subset_closure ⟨2, le_rfl, rfl⟩
  -- The third orbit word is (xy)²x, so cancellation recovers x and then y.
  have hword : (φ ^ 2) (x * y) = (x * y) ^ 2 * x := by
    simp [pow_two, MulAut.mul_apply, map_mul, φ_x, φ_y, mul_assoc]
  rw [hword] at h₂
  have hx : x ∈ H := by simpa using H.mul_mem (H.inv_mem (H.pow_mem hw 2)) h₂
  have hy : y ∈ H := by simpa using H.mul_mem (H.inv_mem hx) hw
  apply top_unique
  rw [← FreeGroup.closure_range_of (Fin 2), Subgroup.closure_le]
  exact Set.range_subset_iff.mpr (Fin.forall_fin_two.mpr ⟨hx, hy⟩)

private theorem two_fail_to_generate :
    Subgroup.closure {z | ∃ i < 2, z = (φ ^ i) (x * y)} ≠ ⊤ := by
  -- In the action on three points, both initial words fix 2, whereas x moves it.
  let π := FreeGroup.lift fun i : Fin 2 =>
    if i = 0 then finRotate 3 else Equiv.swap (1 : Fin 3) 2
  let H := (MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3)).comap π
  have hle : Subgroup.closure {z | ∃ i < 2, z = (φ ^ i) (x * y)} ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have : i = 0 ∨ i = 1 := by omega
    change π ((φ ^ i) (x * y)) 2 = 2
    rcases this with rfl | rfl <;>
      simp only [pow_zero, pow_one, MulAut.one_apply, map_mul, φ_x, φ_y, π, x, y,
        FreeGroup.lift_apply_of] <;> decide
  intro h
  have hx := hle (h ▸ Subgroup.mem_top x)
  change π x 2 = 2 at hx
  simp only [π, x, FreeGroup.lift_apply_of] at hx
  exact (by decide : finRotate 3 2 ≠ 2) hx

/--
**Bogopolski's Cayley–Hamilton analogue fails for free groups (Kourovka 17.32).** There are a
natural number $n$, an element $w$ of the free group $F_n$ of rank $n$ and an automorphism
$\varphi$ of $F_n$ such that $w, \varphi(w), \dots, \varphi^n(w)$ generate $F_n$ but
$w, \varphi(w), \dots, \varphi^{n-1}(w)$ do not.

Ionin and Semidetnov (Answer 8.2) give the example $n = 2$, $F_2 = \langle x, y \rangle$, $w = xy$
and $\varphi(x) = yx$, $\varphi(y) = x$. The Kourovka Notebook (21st issue) answers 17.32 "No, it
is not true", citing their preprint and a preprint of O. Kharlampovich.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.32 (O. V. Bogopolski); resolution: V.
Ionin and A. Semidetnov, On some more problems from the Kourovka Notebook, preprint,
arXiv:2608.29219 (2026; solutions found with the assistance of large language models and checked by
the authors, per its abstract); O. Kharlampovich, preprint (2026), Ionin-Semidetnov, Answer 8.2 (the
assertion fails for n = 2: w = xy, φ(x) = yx, φ(y) = x); the Kourovka Notebook (21st issue) marks
17.32 solved (No, it is not true), https://arxiv.org/abs/2608.29219.
-/
theorem freeGroupCayleyHamilton_refuted : ¬ freeGroupCayleyHamilton := by
  intro h
  exact two_fail_to_generate (h 2 (x * y) φ three_generate)

end MathlibExt.GroupTheory.FreeGroupCayleyHamiltonKourovka17Problem32Wanted
