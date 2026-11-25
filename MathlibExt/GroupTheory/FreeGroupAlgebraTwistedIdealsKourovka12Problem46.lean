/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Twisted right ideals in the group algebra of a free group (Kourovka Notebook Problem 12.46)

We prove the negative answer to Kourovka Problem 12.46. Put $P = xy(xy+yx)$ and
$Q = yx(xy+yx)$. The counterexample is $P+Qx$. A longest reduced word in the support
of either right factor shows that $Pu+Qv=0$ forces $u=v=0$. Twisting scales $P$ and $Q$
by the same character value, while the extra $x$ contributes a factor of $a$.

Kourovka Notebook, Archive of Solved Problems, Problem 12.46 (P. A. Linnell): let `F` be free on `x,
y`, and for `|a| = |b| = 1` let `ϑ_{a,b}` be the automorphism of `ℂF` with `x ↦ a x`, `y ↦ b y`.
Given `0 ≠ α ∈ ℂF`, can we always find `a, b ∈ ℂ ∖ {1}` with `|a| = |b| = 1` such that `α ℂF ∩
ϑ_{a,b}(α) ℂF ≠ 0`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.46 (P. A.
Linnell). UnsolvedMath record UM-00700865 (`KOU-12.46`), dataset ulamai/UnsolvedMath v1.8.0.

`ℂF` is `MonoidAlgebra ℂ F`; `ϑ_{a,b}` multiplies the coefficient of `g` by `χ(g)`, where `χ` is the
character with `χ(x) = a`, `χ(y) = b`, which is the algebra automorphism with `x ↦ a x`, `y ↦ b y`.
A nonzero element of `α ℂF ∩ ϑ_{a,b}(α) ℂF` is written `α β = ϑ_{a,b}(α) γ ≠ 0`; `a, b` are units of
absolute value 1 different from 1.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46Wanted

/-- **Twisting character of the free group of rank two.** Let $F$ be the free group on $x, y$. For
nonzero complex numbers $a, b$, this is the homomorphism $\chi \colon F \to \mathbb{C}^\times$ with
$\chi(x) = a$ and $\chi(y) = b$. -/
noncomputable def twistCharacter (a b : ℂˣ) : FreeGroup (Fin 2) →* ℂˣ :=
  FreeGroup.lift ![a, b]

/-- **Twisting automorphism of the free group algebra.** Let $F$ be the free group on $x, y$, let
$\mathbb{C}F$ be its complex group algebra, and for nonzero complex numbers $a, b$ let $\chi$ be the
character of $F$ with $\chi(x) = a$ and $\chi(y) = b$. The map $\vartheta_{a,b}$ sends
$\alpha = \sum_{g \in F} c_g\, g \in \mathbb{C}F$ to $\sum_{g \in F} \chi(g)\, c_g\, g$.

Since $\chi$ is a homomorphism, $\vartheta_{a,b}$ is the algebra automorphism of $\mathbb{C}F$ with
$\vartheta_{a,b}(x) = a x$ and $\vartheta_{a,b}(y) = b y$. -/
noncomputable def theta (a b : ℂˣ) (α : MonoidAlgebra ℂ (FreeGroup (Fin 2))) :
    MonoidAlgebra ℂ (FreeGroup (Fin 2)) :=
  α.coeff.sum fun g c => MonoidAlgebra.single g ((twistCharacter a b g : ℂ) * c)

/-- **Linnell's twisted right ideal question (Kourovka 12.46).** Let $F$ be the free group on
$x, y$, let $\mathbb{C}F$ be its complex group algebra, and for nonzero complex numbers $a, b$ let
$\vartheta_{a,b}$ be the twisting automorphism of $\mathbb{C}F$ with $\vartheta_{a,b}(x) = a x$ and
$\vartheta_{a,b}(y) = b y$. The assertion is that for every nonzero $\alpha \in \mathbb{C}F$ there
are complex numbers $a, b \neq 1$ with $|a| = |b| = 1$ such that the right ideals
$\alpha\,\mathbb{C}F$ and $\vartheta_{a,b}(\alpha)\,\mathbb{C}F$ intersect nontrivially, that is,
$\alpha\beta = \vartheta_{a,b}(\alpha)\gamma \neq 0$ for some $\beta, \gamma \in \mathbb{C}F$. -/
def twistedRightIdealsIntersect : Prop :=
  ∀ α : MonoidAlgebra ℂ (FreeGroup (Fin 2)), α ≠ 0 →
    ∃ a b : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ ‖(b : ℂ)‖ = 1 ∧ (a : ℂ) ≠ 1 ∧ (b : ℂ) ≠ 1 ∧
      ∃ β γ : MonoidAlgebra ℂ (FreeGroup (Fin 2)), α * β = theta a b α * γ ∧ α * β ≠ 0

open MonoidAlgebra

local notation "F" => FreeGroup (Fin 2)
local notation "R" => MonoidAlgebra ℂ F
local notation "x" => (FreeGroup.of (0 : Fin 2))
local notation "y" => (FreeGroup.of (1 : Fin 2))

-- The four words (xy)(xy), (xy)(yx), (yx)(xy), (yx)(yx) have the same
-- character. In each pair we can choose either last letter.
private def pairWord (i : Bool) : F := if i then y * x else x * y

private def word (i j : Bool) : F := pairWord i * pairWord j

private noncomputable def block (i : Bool) : R :=
  single (word i false) 1 + single (word i true) 1

private def lastIndex (j : Bool) : Fin 2 := if j then 0 else 1

-- For distinct words of equal length, cancelling their common prefix leaves
-- the final letter of the second word intact.
private theorem last_letter :
    ∀ i j k l : Bool, (k, l) ≠ (i, j) →
      ((word k l)⁻¹ * word i j).toWord.getLast? = some (lastIndex j, true) := by
  decide

private theorem length_increases {u g : F} {d : Fin 2}
    (hu : u.toWord.getLast? = some (d, true))
    (hg : g.toWord.head? ≠ some (d, false)) :
    g.toWord.length < (u * g).toWord.length := by
  have hred : FreeGroup.IsReduced (u.toWord ++ g.toWord) := by
    apply List.IsChain.append FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
    rw [hu]
    simp only [Option.mem_some_iff]
    rintro _ rfl ⟨e, sign⟩ he hde
    change d = e at hde
    subst e
    cases sign <;> simp_all
  rw [FreeGroup.toWord_mul, hred.reduce_eq, List.length_append]
  have hu' : u.toWord ≠ [] := fun h => by simp [h] at hu
  have := List.length_pos_iff.mpr hu'
  omega

-- A maximal-length word g in either right factor produces a coefficient that
-- cannot be cancelled: every other contribution would need a longer word.
private theorem blocks_independent (v : Bool → R)
    (h : block false * v false + block true * v true = 0) (i : Bool) : v i = 0 := by
  classical
  by_contra hi
  let s := (v false).coeff.support ∪ (v true).coeff.support
  have hmem (k : Bool) {g : F} (hg : (v k).coeff g ≠ 0) : g ∈ s := by
    cases k <;> simp_all [s, Finsupp.mem_support_iff]
  obtain ⟨g₀, hg₀⟩ := Finsupp.support_nonempty_iff.mpr (mt coeff_eq_zero.mp hi)
  obtain ⟨g, hg, hmax⟩ := s.exists_max_image (fun g => g.toWord.length)
    ⟨g₀, hmem i (Finsupp.mem_support_iff.mp hg₀)⟩
  obtain ⟨k, hk⟩ : ∃ k : Bool, (v k).coeff g ≠ 0 := by
    rcases Finset.mem_union.mp hg with h | h
    · exact ⟨false, Finsupp.mem_support_iff.mp h⟩
    · exact ⟨true, Finsupp.mem_support_iff.mp h⟩
  obtain ⟨j, hj⟩ : ∃ j : Bool, g.toWord.head? ≠ some (lastIndex j, false) := by
    by_cases hhead : g.toWord.head? = some (0, false)
    · exact ⟨false, by simp [lastIndex, hhead]⟩
    · exact ⟨true, hhead⟩
  have vanish (m n : Bool) (hne : (m, n) ≠ (k, j)) :
      (v m).coeff ((word m n)⁻¹ * (word k j * g)) = 0 := by
    by_contra hn
    have hle := hmax _ (hmem m hn)
    have hlt := length_increases (last_letter k j m n hne) hj
    rw [mul_assoc] at hlt
    exact hlt.not_ge hle
  have he := congrArg (fun f : R => f.coeff (word k j * g)) h
  simp only [block, add_mul, coeff_add, Finsupp.add_apply, coeff_single_mul_apply,
    one_mul, coeff_zero, Finsupp.zero_apply] at he
  cases k <;> cases j <;> simp [vanish] at he <;> contradiction

private theorem theta_add (a b : ℂˣ) (u v : R) :
    theta a b (u + v) = theta a b u + theta a b v := by
  classical
  simp [theta, Finsupp.sum_add_index', mul_add, single_add]

private theorem theta_single (a b : ℂˣ) (g : F) :
    theta a b (single g 1) = single g (twistCharacter a b g : ℂ) := by
  classical
  simp [theta, Finsupp.sum_single_index]

private theorem character_word (a b : ℂˣ) (i j : Bool) :
    (twistCharacter a b (word i j) : ℂ) = ((a : ℂ) * b) ^ 2 := by
  cases i <;> cases j <;>
    simp [word, pairWord, twistCharacter, pow_two, mul_comm, mul_left_comm, mul_assoc]

private theorem theta_shifted_block (a b : ℂˣ) (i : Bool) (t : F) :
    theta a b (block i * single t 1) =
      (((a : ℂ) * b) ^ 2 * (twistCharacter a b t : ℂ)) • (block i * single t 1) := by
  simp [block, add_mul, theta_add, theta_single, character_word, smul_add]

private noncomputable def witness : R := block false + block true * single x 1

private theorem witness_ne_zero : witness ≠ 0 := by
  intro h
  have hrel : block false * (1 : R) + block true * single x 1 = 0 := by
    simpa [witness] using h
  have := blocks_independent (fun i => if i then single x 1 else 1) hrel false
  exact one_ne_zero this

private theorem theta_witness (a b : ℂˣ) :
    theta a b witness =
      (((a : ℂ) * b) ^ 2) • block false +
      (((a : ℂ) * b) ^ 2 * a) • (block true * single x 1) := by
  have h := theta_shifted_block a b false 1
  simp only [← one_def, mul_one, map_one, Units.val_one] at h
  rw [witness, theta_add, h, theta_shifted_block]
  simp [twistCharacter]

/--
**Linnell's twisted right ideal question has a negative answer (Kourovka 12.46).** Let $F$ be the
free group on $x, y$, let $\mathbb{C}F$ be its complex group algebra, and for nonzero complex
numbers $a, b$ let $\vartheta_{a,b}$ be the twisting automorphism of $\mathbb{C}F$ with
$\vartheta_{a,b}(x) = a x$ and $\vartheta_{a,b}(y) = b y$. There is a nonzero
$\alpha \in \mathbb{C}F$ such that for all complex numbers $a, b \neq 1$ with $|a| = |b| = 1$
the right ideals $\alpha\,\mathbb{C}F$ and $\vartheta_{a,b}(\alpha)\,\mathbb{C}F$ intersect only in
$0$: whenever $\beta, \gamma \in \mathbb{C}F$ satisfy $\alpha\beta = \vartheta_{a,b}(\alpha)\gamma$,
then $\alpha\beta = 0$.

The Kourovka Archive answers 12.46 "No, not always" (A. V. Tushev, 1995).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.46 (P. A.
Linnell); resolution: A. V. Tushev, Ukrain. Mat. Zh. 47 (1995), no. 4, 571-572, Kourovka Archive,
Problem 12.46: No, not always.
-/
public theorem twistedRightIdealsIntersect_refuted : ¬ twistedRightIdealsIntersect := by
  intro h
  obtain ⟨a, b, _, _, ha, _, β, γ, heq, hne⟩ := h witness witness_ne_zero
  let c := ((a : ℂ) * b) ^ 2
  let X : R := single x 1
  have hrel : block false * (β - c • γ) + block true * (X * (β - (c * a) • γ)) = 0 := by
    rw [theta_witness] at heq
    simp only [witness, add_mul, smul_mul_assoc] at heq
    change block false * β + (block true * X) * β =
      c • (block false * γ) + (c * a) • ((block true * X) * γ) at heq
    rw [← sub_eq_zero] at heq
    simpa only [mul_sub, mul_smul_comm, ← mul_assoc, add_sub_add_comm] using heq
  have hz := blocks_independent (fun i =>
    if i then X * (β - (c * a) • γ) else β - c • γ) hrel
  have hβ : β = c • γ := sub_eq_zero.mp (hz false)
  have hX : X * (β - (c * a) • γ) = 0 := hz true
  have hδ : β - (c * a) • γ = 0 := by
    simpa [X, ← mul_assoc, ← one_def] using congrArg (fun f : R => single x⁻¹ (1 : ℂ) * f) hX
  have hscalar : (c - c * (a : ℂ)) • γ = 0 := by
    simpa only [sub_smul, ← hβ] using hδ
  have hc : c ≠ 0 := pow_ne_zero _ (mul_ne_zero a.ne_zero b.ne_zero)
  have hd : c - c * (a : ℂ) ≠ 0 := by
    simpa only [mul_sub, mul_one] using mul_ne_zero hc (sub_ne_zero.mpr ha.symm)
  have hγ := (smul_eq_zero.mp hscalar).resolve_left hd
  exact hne (by simp [hβ, hγ])

end MathlibExt.GroupTheory.FreeGroupAlgebraTwistedIdealsKourovka12Problem46Wanted
