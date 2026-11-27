/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.BraidGroupShared
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Ring.Aut
import Mathlib.GroupTheory.FreeGroup.Center
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing

/-!
# Torsion-free proper quotients of braid groups

We prove that for every $n \ge 3$ the braid group $B_n$ has a nonabelian torsion-free quotient by
a nontrivial normal subgroup. For $n \ge 5$ this answers Kourovka Notebook Problem 14.102(c).

The proof builds on Artin's representation of $B_n$ by automorphisms of the free group $F_n$ and
on the Magnus expansion, which sends each free generator $x_i$ to $1 + x_i$ in the integral word
algebra on $x_1, \dots, x_n$. Through it, the Artin action becomes an action by ring automorphisms
of the word algebra truncated by keeping the words of length at most $n$. An iterated commutator
of the squares of the first two braid generators acts trivially after truncation. It is
nontrivial in the braid group, as seen by making the product of the first three free generators
the identity and comparing the resulting inner automorphisms of a free group on two generators.

The linear part of the action permutes the strands and exhibits noncommuting images. A
finite-order element with identity linear part is trivial by the degree filtration. For an
element of prime order $p$ with a $p$-cycle, take the successive images of one orbit variable
as coordinates. After deleting the other variables, the boundary product is rotation-invariant.
The sum of its degree-$p$ coefficients is divisible by $p$. Specialization to one variable
sends the boundary product to $(1+X)^p$, whose degree-$p$ coefficient is one.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.102 (V. Lin; V. Shpilrain); part (c) in
the Archive of Solved Problems. UnsolvedMath record UM-00701086 (`KOU-14.102`), dataset
ulamai/UnsolvedMath v1.8.0.
-/

namespace MathlibExt.GroupTheory.BraidGroupEndomorphismsKourovka14Problem102Wanted

open MathlibExt.GroupTheory.BraidGroupShared (BraidGroup)

@[expose] public section

/-- **Kourovka Problem 14.102(c): torsion-free quotients of braid groups.** The statement that for
every $n > 4$, the braid group $B_n$ on $n$ strands has a nontrivial normal subgroup $N$ such that
the quotient $B_n / N$ is non-abelian and torsion-free (no element other than the identity has
finite order). Posed by V. Lin and V. Shpilrain. -/
def braidTorsionFreeNonabelianProperQuotient : Prop :=
  ∀ n : ℕ, 4 < n → ∃ (N : Subgroup (BraidGroup n)) (_ : N.Normal), N ≠ ⊥ ∧
    (∃ x y : BraidGroup n ⧸ N, x * y ≠ y * x) ∧
    ∀ x : BraidGroup n ⧸ N, x ≠ 1 → ¬ IsOfFinOrder x

end

noncomputable section

open scoped MonoidAlgebra commutatorElement

/-! ## The word algebra and its degree filtration -/

private abbrev WordRing (ι : Type) := ℤ[FreeMonoid ι]

private def degreeGE {ι : Type} (k : ℕ) (x : WordRing ι) : Prop :=
  ∀ w : FreeMonoid ι, w.toList.length < k → x.coeff w = 0

private theorem degreeGE_add {ι : Type} {k : ℕ} {x y : WordRing ι}
    (hx : degreeGE k x) (hy : degreeGE k y) : degreeGE k (x + y) := by
  intro w hw
  simp [hx w hw, hy w hw]

private theorem degreeGE_mul {ι : Type} {j k : ℕ} {x y : WordRing ι}
    (hx : degreeGE j x) (hy : degreeGE k y) : degreeGE (j + k) (x * y) := by
  classical
  intro w hw
  rw [MonoidAlgebra.coeff_mul]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  dsimp only
  split_ifs with huv
  · subst w
    rw [FreeMonoid.toList_mul, List.length_append] at hw
    have hn : u.toList.length < j ∨ v.toList.length < k := by omega
    cases hn with
    | inl h => simp [hx u h]
    | inr h => simp [hy v h]
  · rfl

private def truncIdeal (ι : Type) (k : ℕ) : TwoSidedIdeal (WordRing ι) :=
  TwoSidedIdeal.mk' { x | degreeGE k x }
    (by intro w _; simp)
    (fun hx hy => degreeGE_add hx hy)
    (by intro x hx w hw; simpa using hx w hw)
    (fun {x _} hy => by simpa using degreeGE_mul (x := x) (j := 0) (by simp [degreeGE]) hy)
    (fun {_ y} hx => by simpa using degreeGE_mul (y := y) (k := 0) hx (by simp [degreeGE]))

private abbrev Trunc (ι : Type) (k : ℕ) := (truncIdeal ι k).ringCon.Quotient

private def trunc {ι : Type} (k : ℕ) : WordRing ι →+* Trunc ι k :=
  (truncIdeal ι k).ringCon.mk'

private theorem trunc_surj {ι : Type} (k : ℕ) :
    Function.Surjective (trunc (ι := ι) k) :=
  RingCon.mk'_surjective _

private theorem trunc_eq_zero {ι : Type} (k : ℕ) (x : WordRing ι) :
    trunc k x = 0 ↔ degreeGE k x := by
  rw [← TwoSidedIdeal.mem_ker, trunc, TwoSidedIdeal.ker_ringCon_mk']
  exact TwoSidedIdeal.mem_mk' ..

private def coeff {ι : Type} {k : ℕ} (w : FreeMonoid ι) (hw : w.toList.length < k) :
    Trunc ι k →+ ℤ where
  toFun := Quotient.lift (fun x => x.coeff w) (fun x y h => by
    have hxy : degreeGE k (x - y) := h
    simpa [sub_eq_zero] using hxy w hw)
  map_zero' := by change (0 : WordRing ι).coeff w = 0; simp
  map_add' := by
    intro x y
    obtain ⟨a, rfl⟩ := trunc_surj k x
    obtain ⟨b, rfl⟩ := trunc_surj k y
    change (a + b).coeff w = a.coeff w + b.coeff w
    simp

private theorem coeff_trunc {ι : Type} {k : ℕ} (w : FreeMonoid ι) (hw : w.toList.length < k)
    (x : WordRing ι) : coeff w hw (trunc k x) = x.coeff w := rfl

private def level {ι : Type} {k : ℕ} (d : ℕ) (x : Trunc ι k) : Prop :=
  ∃ y, degreeGE d y ∧ trunc k y = x

private theorem level_zero {ι : Type} {k d : ℕ} : level d (0 : Trunc ι k) :=
  ⟨0, by intro w hw; simp, map_zero _⟩

private theorem level_univ {ι : Type} {k : ℕ} (x : Trunc ι k) : level 0 x := by
  obtain ⟨y, rfl⟩ := trunc_surj k x
  exact ⟨y, by simp [degreeGE], rfl⟩

private theorem level_mono {ι : Type} {k d e : ℕ} {x : Trunc ι k}
    (h : d ≤ e) : level e x → level d x := by
  rintro ⟨y, hy, rfl⟩
  exact ⟨y, fun w hw => hy w (hw.trans_le h), rfl⟩

private theorem level_eq_zero {ι : Type} {k d : ℕ} {x : Trunc ι k}
    (hk : k ≤ d) : level d x → x = 0 := by
  rintro ⟨y, hy, rfl⟩
  exact (trunc_eq_zero k y).2 fun w hw => hy w (hw.trans_le hk)

private theorem level_add {ι : Type} {k d : ℕ} {x y : Trunc ι k}
    (hx : level d x) (hy : level d y) : level d (x + y) := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact ⟨x + y, degreeGE_add hx hy, map_add _ _ _⟩

private theorem level_neg {ι : Type} {k d : ℕ} {x : Trunc ι k}
    (hx : level d x) : level d (-x) := by
  obtain ⟨x, hx, rfl⟩ := hx
  exact ⟨-x, by intro w hw; simp [hx w hw], map_neg _ _⟩

private theorem level_sub {ι : Type} {k d : ℕ} {x y : Trunc ι k}
    (hx : level d x) (hy : level d y) : level d (x - y) := by
  rw [sub_eq_add_neg]
  exact level_add hx (level_neg hy)

private theorem level_mul {ι : Type} {k d e : ℕ} {x y : Trunc ι k}
    (hx : level d x) (hy : level e y) : level (d + e) (x * y) := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact ⟨x * y, degreeGE_mul hx hy, map_mul _ _ _⟩

private theorem level_zsmul {ι : Type} {k d : ℕ} (z : ℤ) {x : Trunc ι k}
    (hx : level d x) : level d (z • x) := by
  obtain ⟨x, hx, rfl⟩ := hx
  refine ⟨z • x, ?_, map_zsmul _ _ _⟩
  intro w hw
  rw [MonoidAlgebra.coeff_smul_apply, hx w hw, smul_zero]

private abbrev word {ι : Type} {k : ℕ} (w : FreeMonoid ι) : Trunc ι k :=
  trunc k (MonoidAlgebra.of ℤ (FreeMonoid ι) w)

private abbrev var {ι : Type} {k : ℕ} (i : ι) : Trunc ι k := word (FreeMonoid.of i)

private theorem word_level {ι : Type} {k : ℕ} (w : FreeMonoid ι) :
    level w.toList.length (word (k := k) w) := by
  classical
  refine ⟨_, ?_, rfl⟩
  intro u hu
  have hwu : w ≠ u := by rintro rfl; omega
  simp [MonoidAlgebra.of, hwu]

private theorem var_level {ι : Type} {k : ℕ} (i : ι) : level 1 (var (k := k) i) :=
  word_level (FreeMonoid.of i)

private theorem lift_level {ι κ : Type} {k : ℕ} {f : ι → Trunc κ k}
    (hf : ∀ i, level 1 (f i)) (w : FreeMonoid ι) :
    level w.toList.length (FreeMonoid.lift f w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact level_univ _
  | of_mul i w ih =>
    simpa only [map_mul, FreeMonoid.lift_eval_of, FreeMonoid.toList_of_mul, List.length_cons,
      Nat.add_comm] using level_mul (hf i) ih

private theorem substAux_level {ι κ : Type} {k d : ℕ} {f : ι → Trunc κ k}
    (hf : ∀ i, level 1 (f i)) {x : WordRing ι} (hx : degreeGE d x) :
    level d (MonoidAlgebra.lift ℤ (Trunc κ k) (FreeMonoid ι) (FreeMonoid.lift f) x) := by
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  classical
  induction x.coeff.support using Finset.induction_on with
  | empty => simpa using level_zero
  | insert w s hw ih =>
    rw [Finset.sum_insert hw]
    apply level_add _ ih
    by_cases h : w.toList.length < d
    · simpa [hx w h] using (level_zero (ι := κ) (k := k) (d := d))
    · exact level_zsmul _ (level_mono (Nat.le_of_not_lt h) (lift_level hf w))

private def subst {ι κ : Type} {k : ℕ} (f : ι → Trunc κ k) (hf : ∀ i, level 1 (f i)) :
    Trunc ι k →+* Trunc κ k :=
  let F := (MonoidAlgebra.lift ℤ (Trunc κ k) (FreeMonoid ι) (FreeMonoid.lift f)).toRingHom
  (truncIdeal ι k).ringCon.lift F (by
    intro x y h
    have hxy : degreeGE k (x - y) := h
    change F x = F y
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact level_eq_zero le_rfl (substAux_level hf hxy))

private theorem subst_level {ι κ : Type} {k d : ℕ} {f : ι → Trunc κ k}
    (hf : ∀ i, level 1 (f i)) {x : Trunc ι k} (hx : level d x) :
    level d (subst f hf x) := by
  obtain ⟨x, hx, rfl⟩ := hx
  exact substAux_level hf hx

private theorem subst_var {ι κ : Type} {k : ℕ} (f : ι → Trunc κ k)
    (hf : ∀ i, level 1 (f i)) (i : ι) : subst f hf (var i) = f i := by
  change MonoidAlgebra.lift ℤ _ _ (FreeMonoid.lift f) (MonoidAlgebra.of ℤ _ (FreeMonoid.of i)) = _
  simp

private theorem hom_ext {ι : Type} {k : ℕ} {R : Type} [Ring R]
    {F G : Trunc ι k →+* R} (h : ∀ i, F (var i) = G (var i)) : F = G := by
  have hw : ∀ w : FreeMonoid ι, F (word w) = G (word w) := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one =>
      change F ((trunc k) ((MonoidAlgebra.of ℤ (FreeMonoid ι)) 1)) =
        G ((trunc k) ((MonoidAlgebra.of ℤ (FreeMonoid ι)) 1))
      simp only [map_one]
    | of_mul i w ih =>
      have hw : word (k := k) (FreeMonoid.of i * w) = var i * word w := by
        unfold word
        rw [map_mul, map_mul]
      rw [hw, map_mul, map_mul, h, ih]
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := trunc_surj k x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single w z =>
    have hs : MonoidAlgebra.single w z = z • MonoidAlgebra.of ℤ (FreeMonoid ι) w := by
      simp [MonoidAlgebra.of_apply]
    rw [hs, map_zsmul, map_zsmul, map_zsmul]
    rw [hw]

private theorem level_iff {ι : Type} {k d : ℕ} {x : Trunc ι k} (h : d ≤ k) :
    level d x ↔ ∀ w (hw : w.toList.length < d), coeff w (hw.trans_le h) x = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩ w hw
    exact hx w hw
  · obtain ⟨x, rfl⟩ := trunc_surj k x
    exact fun hx => ⟨x, hx, rfl⟩

private theorem subst_eq {ι κ : Type} {k : ℕ} (F : Trunc ι k →+* Trunc κ k)
    (h : ∀ i, level 1 (F (var i))) : subst (fun i => F (var i)) h = F :=
  hom_ext fun i => subst_var _ _ i

private theorem lift_diff_level {ι κ : Type} {k e : ℕ} {f g : ι → Trunc κ k}
    (hf : ∀ i, level 1 (f i)) (hg : ∀ i, level 1 (g i))
    (hfg : ∀ i, level (1 + e) (f i - g i)) (w : FreeMonoid ι) :
    level (w.toList.length + e) (FreeMonoid.lift f w - FreeMonoid.lift g w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one, sub_self]; exact level_zero
  | of_mul i w ih =>
    simp only [map_mul, FreeMonoid.lift_eval_of, FreeMonoid.toList_of_mul, List.length_cons]
    rw [show f i * FreeMonoid.lift f w - g i * FreeMonoid.lift g w =
        (f i - g i) * FreeMonoid.lift f w + g i * (FreeMonoid.lift f w - FreeMonoid.lift g w) by
      noncomm_ring]
    exact level_add
      (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        level_mul (hfg i) (lift_level hf w))
      (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using level_mul (hg i) ih)

private theorem subst_diff_level {ι κ : Type} {k d e : ℕ}
    {f g : ι → Trunc κ k} (hf : ∀ i, level 1 (f i)) (hg : ∀ i, level 1 (g i))
    (hfg : ∀ i, level (1 + e) (f i - g i)) {x : Trunc ι k} (hx : level d x) :
    level (d + e) (subst f hf x - subst g hg x) := by
  obtain ⟨x, hx, rfl⟩ := hx
  change level _ (MonoidAlgebra.lift ℤ _ _ (FreeMonoid.lift f) x -
    MonoidAlgebra.lift ℤ _ _ (FreeMonoid.lift g) x)
  simp only [MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_sub_distrib, ← smul_sub]
  classical
  induction x.coeff.support using Finset.induction_on with
  | empty => simpa using level_zero
  | insert w s hw ih =>
    rw [Finset.sum_insert hw]
    refine level_add ?_ ih
    by_cases h : w.toList.length < d
    · simpa [hx w h] using (level_zero (ι := κ) (k := k) (d := d + e))
    · exact level_zsmul _ (level_mono (by omega) (lift_diff_level hf hg hfg w))

private theorem hom_diff_level {ι κ : Type} {k d e : ℕ}
    {F G : Trunc ι k →+* Trunc κ k} (hf : ∀ i, level 1 (F (var i)))
    (hg : ∀ i, level 1 (G (var i))) (hfg : ∀ i, level (1 + e) (F (var i) - G (var i)))
    {x : Trunc ι k} (hx : level d x) : level (d + e) (F x - G x) := by
  simpa only [subst_eq F hf, subst_eq G hg] using subst_diff_level hf hg hfg hx

/-! ## Endomorphisms with identity linear part -/

private def delta {ι : Type} {k : ℕ} (F : Trunc ι k →+* Trunc ι k) : AddMonoid.End (Trunc ι k) :=
  F.toAddMonoidHom - AddMonoidHom.id _

private theorem delta_shift {ι : Type} {k d : ℕ} {F : Trunc ι k →+* Trunc ι k}
    (h : ∀ i, level 2 (F (var i) - var i)) {x : Trunc ι k} (hx : level d x) :
    level (d + 1) (delta F x) := by
  have hf : ∀ i, level 1 (F (var i)) := fun i => by
    simpa using level_add (level_mono (by decide : 1 ≤ 2) (h i)) (var_level (k := k) i)
  exact hom_diff_level (G := RingHom.id _) (e := 1) hf var_level h hx

private theorem delta_nilpotent {ι : Type} {k : ℕ} {F : Trunc ι k →+* Trunc ι k}
    (h : ∀ i, level 2 (F (var i) - var i)) : IsNilpotent (delta F) := by
  have hd (m : ℕ) (x : Trunc ι k) : level m ((delta F ^ m) x) := by
    induction m with
    | zero => exact level_univ _
    | succ m ih =>
      rw [pow_succ']
      exact delta_shift h ih
  exact ⟨k, AddMonoidHom.ext fun x => level_eq_zero le_rfl (hd k x)⟩

private theorem triangular_bijective {ι : Type} {k : ℕ} (F : Trunc ι k →+* Trunc ι k)
    (h : ∀ i, level 2 (F (var i) - var i)) : Function.Bijective F := by
  have hu := (delta_nilpotent h).isUnit_add_one
  have he : delta F + 1 = F.toAddMonoidHom := by
    ext x
    change F x - x + x = F x
    abel
  rw [he] at hu
  obtain ⟨u, hu⟩ := hu
  have hi (x : Trunc ι k) : (↑u⁻¹ : AddMonoid.End (Trunc ι k)) (F x) = x := by
    change (↑u⁻¹ : AddMonoid.End _) (F.toAddMonoidHom x) = x
    rw [← hu]
    change ((↑(u⁻¹) : AddMonoid.End (Trunc ι k)) * (↑u : AddMonoid.End (Trunc ι k))) x = x
    rw [Units.inv_mul]
    rfl
  have hs (x : Trunc ι k) : F ((↑u⁻¹ : AddMonoid.End (Trunc ι k)) x) = x := by
    change F.toAddMonoidHom ((↑u⁻¹ : AddMonoid.End _) x) = x
    rw [← hu]
    change ((↑u : AddMonoid.End (Trunc ι k)) * (↑(u⁻¹) : AddMonoid.End (Trunc ι k))) x = x
    rw [Units.mul_inv]
    rfl
  exact ⟨Function.LeftInverse.injective hi, Function.RightInverse.surjective hs⟩

private theorem triangular_no_torsion {ι : Type} {k : ℕ} {F : RingAut (Trunc ι k)}
    (h : ∀ i, level 2 (F (var i) - var i)) {m : ℕ} (hm : 0 < m) (hpow : F ^ m = 1) :
    F = 1 := by
  have shift {d : ℕ} {x : Trunc ι k} (hx : level d x) : level (d + 1) (F x - x) :=
    delta_shift (F := F.toRingHom) h hx
  have ht : ∀ d ≤ k, ∀ x : Trunc ι k, level d (F x - x) := by
    intro d
    induction d with
    | zero => exact fun _ x => level_univ _
    | succ d ih =>
      intro hd x
      have hi := ih (by omega) x
      have step (q : ℕ) : level (d + 1) ((F ^ q) x - x - q • (F x - x)) := by
        induction q with
        | zero => simpa using level_zero
        | succ q hq =>
          have hr : level d ((F ^ q) x - x) := by
            have hz : level d (q • (F x - x)) := by
              simpa only [natCast_zsmul] using level_zsmul (q : ℤ) hi
            simpa using level_add (level_mono (Nat.le_succ d) hq) hz
          have hshift := shift hr
          rw [map_sub] at hshift
          rw [pow_succ', RingAut.mul_apply, succ_nsmul]
          rw [show F ((F ^ q) x) - x - (q • (F x - x) + (F x - x)) =
              (F ((F ^ q) x) - F x - ((F ^ q) x - x)) +
                ((F ^ q) x - x - q • (F x - x)) by abel]
          exact level_add hshift hq
      have hs := step m
      rw [hpow, RingAut.one_apply, sub_self, zero_sub] at hs
      have hn : level (d + 1) (m • (F x - x)) := by simpa using level_neg hs
      rw [level_iff hd] at hn ⊢
      intro w hw
      have hh := hn w hw
      rw [map_nsmul, nsmul_eq_mul] at hh
      exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hm.ne')
  ext x
  exact sub_eq_zero.mp (level_eq_zero le_rfl (ht k le_rfl x))

/-! ## The truncated Magnus expansion -/

private theorem var_nilpotent {ι : Type} {k : ℕ} (i : ι) : IsNilpotent (var (k := k) i) := by
  have hp (d : ℕ) : level d (var (k := k) i ^ d) := by
    induction d with
    | zero => exact level_univ _
    | succ d ih => rw [pow_succ]; exact level_mul ih (var_level i)
  exact ⟨k, level_eq_zero le_rfl (hp k)⟩

private def varUnit {ι : Type} {k : ℕ} (i : ι) : (Trunc ι k)ˣ :=
  (var_nilpotent (k := k) i).isUnit_one_add.unit

private theorem coe_varUnit {ι : Type} {k : ℕ} (i : ι) :
    (↑(varUnit (k := k) i) : Trunc ι k) = 1 + var i :=
  IsUnit.unit_spec _

private def magnus {ι : Type} {k : ℕ} : FreeGroup ι →* (Trunc ι k)ˣ :=
  FreeGroup.lift varUnit

private theorem magnus_apply_of {ι : Type} {k : ℕ} (i : ι) :
    magnus (FreeGroup.of i) = varUnit (k := k) i :=
  FreeGroup.lift_apply_of

private theorem mul_sub_one_level {R : Type} {k : ℕ} {a b : Trunc R k}
    (ha : level 1 (a - 1)) (hb : level 1 (b - 1)) : level 1 (a * b - 1) := by
  rw [show a * b - 1 = a * (b - 1) + (a - 1) by noncomm_ring]
  exact level_add (level_mul (level_univ a) hb) ha

private theorem unit_inv_sub_one_level {R : Type} {k : ℕ} {u : (Trunc R k)ˣ}
    (h : level 1 ((u : Trunc R k) - 1)) : level 1 ((↑(u⁻¹) : Trunc R k) - 1) := by
  have he : (↑(u⁻¹) : Trunc R k) - 1 = -((↑(u⁻¹) : Trunc R k) * ((u : Trunc R k) - 1)) := by
    simp [mul_sub, ← Units.val_mul]
  rw [he]
  exact level_neg (level_mul (level_univ _) h)

private theorem magnus_level {ι : Type} {k : ℕ} (x : FreeGroup ι) :
    level 1 ((magnus (k := k) x).val - 1) := by
  induction x with
  | one => simpa using level_zero
  | of i => simpa [magnus, coe_varUnit] using (var_level (k := k) i)
  | inv_of i =>
    rw [map_inv]
    apply unit_inv_sub_one_level
    simpa [magnus, coe_varUnit] using (var_level (k := k) i)
  | mul x y hx hy => rw [map_mul, Units.val_mul]; exact mul_sub_one_level hx hy

private def liftMagnus {ι : Type} {k : ℕ} (f : MulAut (FreeGroup ι)) :
    Trunc ι k →+* Trunc ι k :=
  subst (fun i => (magnus (k := k) (f (FreeGroup.of i))).val - 1) fun _ => magnus_level _

private theorem liftMagnus_var {ι : Type} {k : ℕ} (f : MulAut (FreeGroup ι)) (i : ι) :
    liftMagnus f (var i) = (magnus (k := k) (f (FreeGroup.of i))).val - 1 :=
  subst_var _ _ _

private theorem liftMagnus_natural {ι : Type} {k : ℕ} (f : MulAut (FreeGroup ι))
    (x : FreeGroup ι) :
    Units.map ((liftMagnus (k := k) f).toMonoidHom) (magnus x) = magnus (f x) := by
  have he : (Units.map ((liftMagnus (k := k) f).toMonoidHom)).comp magnus =
      magnus.comp f.toMonoidHom := by
    apply FreeGroup.ext_hom
    intro i
    apply Units.ext
    simp only [MonoidHom.comp_apply, Units.coe_map,
      MulEquiv.coe_toMonoidHom]
    change liftMagnus (k := k) f (magnus (FreeGroup.of i)).val =
      (magnus (k := k) (f (FreeGroup.of i))).val
    rw [show magnus (FreeGroup.of i) = varUnit (k := k) i from FreeGroup.lift_apply_of,
      coe_varUnit, map_add, map_one, liftMagnus_var]
    abel
  exact DFunLike.congr_fun he x

private theorem liftMagnus_one {ι : Type} {k : ℕ} :
    liftMagnus (k := k) (1 : MulAut (FreeGroup ι)) = RingHom.id _ := by
  apply hom_ext
  intro i
  rw [liftMagnus_var, MulAut.one_apply]
  change (magnus (k := k) (FreeGroup.of i)).val - 1 = var i
  rw [show magnus (FreeGroup.of i) = varUnit (k := k) i from FreeGroup.lift_apply_of,
    coe_varUnit]
  abel

private theorem liftMagnus_mul {ι : Type} {k : ℕ} (f g : MulAut (FreeGroup ι)) :
    liftMagnus (k := k) (f * g) = (liftMagnus f).comp (liftMagnus g) := by
  apply hom_ext
  intro i
  rw [RingHom.comp_apply, liftMagnus_var, liftMagnus_var, map_sub, map_one, MulAut.mul_apply]
  exact congrArg (fun u : (Trunc ι k)ˣ => (↑u : Trunc ι k) - 1)
    (liftMagnus_natural f (g (FreeGroup.of i))).symm

private def magnusAut {ι : Type} (k : ℕ) :
    MulAut (FreeGroup ι) →* RingAut (Trunc ι k) where
  toFun f :=
    { liftMagnus f with
      invFun := liftMagnus f⁻¹
      left_inv := fun x => by
        have he := DFunLike.congr_fun (liftMagnus_mul (k := k) f⁻¹ f) x
        rw [inv_mul_cancel, liftMagnus_one] at he
        exact he.symm
      right_inv := fun x => by
        have he := DFunLike.congr_fun (liftMagnus_mul (k := k) f f⁻¹) x
        rw [mul_inv_cancel, liftMagnus_one] at he
        exact he.symm }
  map_one' := RingEquiv.toRingHom_injective liftMagnus_one
  map_mul' _ _ := RingEquiv.toRingHom_injective (liftMagnus_mul _ _)

private theorem conjugate_var_diff {ι : Type} {k : ℕ} (i : ι) (x : FreeGroup ι) :
    level 2 ((magnus (k := k) x * varUnit i * (magnus (k := k) x)⁻¹).val - 1 - var i) := by
  have h := magnus_level (k := k) x
  let u : (Trunc ι k)ˣ := magnus x
  have h' := unit_inv_sub_one_level (u := u) h
  have he : (u * varUnit (k := k) i * u⁻¹).val - 1 - var i =
      ((↑u : Trunc ι k) - 1) * var i * (↑(u⁻¹) : Trunc ι k) +
        var i * ((↑(u⁻¹) : Trunc ι k) - 1) := by
    rw [Units.val_mul, Units.val_mul, coe_varUnit, mul_add, mul_one, add_mul,
      Units.mul_inv]
    noncomm_ring
  change level 2 ((u * varUnit i * u⁻¹).val - 1 - var i)
  rw [he]
  exact level_add (level_mul (level_mul h (var_level i)) (level_univ _))
    (level_mul (var_level i) h')

private theorem var_sub_level_two_iff {ι : Type} {k : ℕ} (hk : 2 ≤ k) (i j : ι) :
    level 2 (var (k := k) i - var j) ↔ i = j := by
  classical
  constructor
  · intro h
    have hc := (level_iff hk).mp h (FreeMonoid.of i) (show 1 < 2 by decide)
    rw [map_sub, sub_eq_zero] at hc
    by_contra hne
    have hj : FreeMonoid.of j ≠ FreeMonoid.of i := fun e =>
      hne (FreeMonoid.of_injective e).symm
    simp [coeff_trunc, MonoidAlgebra.of, hj] at hc
  · rintro rfl
    simpa using level_zero

/-! ## Coefficients under relabeling and specialization -/

private theorem subst_word {ι κ : Type} {k : ℕ} {f : ι → Trunc κ k}
    (hf : ∀ i, level 1 (f i)) (w : FreeMonoid ι) :
    subst f hf (word w) = FreeMonoid.lift f w := by
  change MonoidAlgebra.lift ℤ _ _ (FreeMonoid.lift f) (MonoidAlgebra.of ℤ _ w) = _
  exact MonoidAlgebra.lift_of _ _

private def relabel {ι κ : Type} {k : ℕ} (f : ι → κ) : Trunc ι k →+* Trunc κ k :=
  subst (var ∘ f) (fun i => var_level (f i))

private theorem relabel_var {ι κ : Type} {k : ℕ} (f : ι → κ) (i : ι) :
    relabel (k := k) f (var i) = var (f i) := subst_var _ _ _

private theorem relabel_word {ι κ : Type} {k : ℕ} (f : ι → κ) (w : FreeMonoid ι) :
    relabel (k := k) f (word w) = word (FreeMonoid.map f w) := by
  rw [relabel, subst_word]
  have h : FreeMonoid.lift (var ∘ f : ι → Trunc κ k) =
      ((trunc k).toMonoidHom.comp (MonoidAlgebra.of ℤ (FreeMonoid κ))).comp
        (FreeMonoid.map f) := by
    apply FreeMonoid.hom_eq
    intro i
    simp [var, word]
  rw [h]
  rfl

private theorem addHom_ext_word {ι : Type} {k : ℕ} {G : Type} [AddCommGroup G]
    {F G' : Trunc ι k →+ G} (h : ∀ w, F (word w) = G' (word w)) : F = G' := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := trunc_surj k x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single w z =>
    have hs : MonoidAlgebra.single w z = z • MonoidAlgebra.of ℤ (FreeMonoid ι) w := by
      simp [MonoidAlgebra.of_apply]
    rw [hs, map_zsmul, map_zsmul, map_zsmul, h]

private def rawHeadCoeff {ι : Type} (d : ℕ) (i : ι) : WordRing ι →+ ℤ := by
  classical
  exact (Finsupp.liftAddHom fun w : FreeMonoid ι =>
    if w.toList.length = d ∧ w.toList.head? = some i then AddMonoidHom.id ℤ else 0).comp
      MonoidAlgebra.coeffAddEquiv.toAddMonoidHom

private theorem rawHeadCoeff_eq {ι : Type} [DecidableEq ι] (d : ℕ) (i : ι) (x : WordRing ι) :
    rawHeadCoeff d i x = x.coeff.sum fun w z =>
      if w.toList.length = d ∧ w.toList.head? = some i then z else 0 := by
  classical
  simp only [rawHeadCoeff, AddMonoidHom.comp_apply, Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro w _
  split_ifs <;> rfl

private def headCoeff {ι : Type} {k d : ℕ} (hd : d < k) (i : ι) : Trunc ι k →+ ℤ :=
  (truncIdeal ι k).ringCon.toAddCon.lift (rawHeadCoeff d i) (by
    classical
    intro x y h
    have hxy : degreeGE k (x - y) := h
    change rawHeadCoeff d i x = rawHeadCoeff d i y
    rw [← sub_eq_zero, ← map_sub, rawHeadCoeff_eq, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hh : w.toList.length = d ∧ w.toList.head? = some i
    · rw [ite_eq_left hh]
      exact hxy w (hh.1 ▸ hd)
    · simp [hh])

private theorem headCoeff_word {ι : Type} [DecidableEq ι] {k d : ℕ} (hd : d < k)
    (i : ι) (w : FreeMonoid ι) :
    headCoeff hd i (word w) =
      if w.toList.length = d ∧ w.toList.head? = some i then 1 else 0 := by
  classical
  change rawHeadCoeff d i (MonoidAlgebra.of ℤ _ w) = _
  rw [rawHeadCoeff_eq, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

private theorem headCoeff_relabel {ι : Type} {k d : ℕ} (hd : d < k) (p : Equiv.Perm ι)
    (i : ι) (x : Trunc ι k) :
    headCoeff hd (p i) (relabel p x) = headCoeff hd i x := by
  classical
  have he : (headCoeff hd (p i)).comp (relabel p).toAddMonoidHom = headCoeff hd i := by
    apply addHom_ext_word
    intro w
    change headCoeff hd (p i) (relabel p (word w)) = headCoeff hd i (word w)
    simp only [relabel_word, headCoeff_word, FreeMonoid.toList_map, List.length_map,
      List.head?_map]
    cases w.toList.head? <;> simp [p.injective.eq_iff]
  exact DFunLike.congr_fun he x

private abbrev scalar {ι : Type} {k : ℕ} : Trunc ι k →+* Trunc Unit k :=
  relabel fun _ => ()

private def repeatedWord (d : ℕ) : FreeMonoid Unit := FreeMonoid.ofList (List.replicate d ())

private theorem unit_word_eq (w : FreeMonoid Unit) : w = repeatedWord w.toList.length := by
  apply FreeMonoid.ext
  change w.toList = List.replicate w.toList.length ()
  induction w.toList with
  | nil => rfl
  | cons a t ih => cases a; exact congrArg (List.cons ()) ih

private abbrev repeatedCoeff {k d : ℕ} (hd : d < k) : Trunc Unit k →+ ℤ :=
  coeff (repeatedWord d) (by simpa [repeatedWord] using hd)

private theorem scalar_coeff_word {ι : Type} {k d : ℕ} (hd : d < k) (w : FreeMonoid ι) :
    repeatedCoeff hd (scalar (word w : Trunc ι k)) =
      if w.toList.length = d then 1 else 0 := by
  classical
  rw [relabel_word]
  rw [unit_word_eq (FreeMonoid.map (fun _ => ()) w)]
  simp only [FreeMonoid.toList_map, List.length_map, word, repeatedCoeff, coeff_trunc,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  have he : ∀ m : ℕ, repeatedWord m = repeatedWord d ↔ m = d := fun m =>
    ⟨fun h => by simpa [repeatedWord] using congrArg (fun w : FreeMonoid Unit => w.toList.length) h,
      fun h => congrArg repeatedWord h⟩
  simp [Finsupp.single_apply, he]

private theorem addHom_sum_apply {ι M G : Type} [Fintype ι] [AddZeroClass M] [AddCommMonoid G]
    (f : ι → M →+ G) (x : M) : (∑ i, f i) x = ∑ i, f i x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem scalar_coeff_sum {ι : Type} [Fintype ι] {k d : ℕ} (hd : d < k) (hp : 0 < d)
    (x : Trunc ι k) :
    repeatedCoeff hd (scalar x) = ∑ i : ι, headCoeff hd i x := by
  classical
  have he : (repeatedCoeff hd).comp scalar.toAddMonoidHom =
      ∑ i : ι, headCoeff hd i := by
    apply addHom_ext_word
    intro w
    change repeatedCoeff hd (scalar (word w)) =
      (∑ i : ι, headCoeff hd i) (word w)
    rw [scalar_coeff_word hd, addHom_sum_apply]
    simp_rw [headCoeff_word]
    split_ifs with h
    · cases hw : w.toList with
      | nil => simp [hw] at h; omega
      | cons i t =>
        have hlen : t.length + 1 = d := by simpa [hw] using h
        simp [hlen]
    · exact (Finset.sum_eq_zero fun i _ => by simp [h]).symm
  have h := DFunLike.congr_fun he x
  change repeatedCoeff hd (scalar x) = (∑ i : ι, headCoeff hd i) x at h
  rwa [addHom_sum_apply] at h

private theorem scalar_comm {k : ℕ} (x y : Trunc Unit k) : x * y = y * x := by
  let : CommMonoid (FreeMonoid Unit) :=
    { (inferInstance : Monoid (FreeMonoid Unit)) with
      mul_comm := fun u v => by
        rw [unit_word_eq (u * v), unit_word_eq (v * u)]
        simp only [FreeMonoid.toList_mul, List.length_append, Nat.add_comm] }
  obtain ⟨x, rfl⟩ := trunc_surj k x
  obtain ⟨y, rfl⟩ := trunc_surj k y
  rw [← map_mul, ← map_mul]
  exact congrArg (trunc k) (mul_comm x y)

private theorem scalar_coeff_pow {k d : ℕ} (hd : d < k) :
    repeatedCoeff hd ((1 + var () : Trunc Unit k) ^ d) = 1 := by
  classical
  have hpow (m : ℕ) : (var () : Trunc Unit k) ^ m = word (repeatedWord m) := by
    unfold var word
    rw [← map_pow, ← map_pow]
    congr 2
    have hlen : (FreeMonoid.of () ^ m).toList.length = m := by
      induction m with
      | zero => rfl
      | succ m ih =>
        simp only [pow_succ, FreeMonoid.toList_mul, List.length_append, FreeMonoid.toList_of, ih]
        rfl
    simpa only [hlen] using unit_word_eq (FreeMonoid.of () ^ m)
  have hc (m : ℕ) :
      repeatedCoeff hd ((var () : Trunc Unit k) ^ m) = if m = d then 1 else 0 := by
    rw [hpow m]
    simp only [word, repeatedCoeff, coeff_trunc, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
    have he : repeatedWord m = repeatedWord d ↔ m = d :=
      ⟨fun h => by
        simpa [repeatedWord] using congrArg (fun w : FreeMonoid Unit => w.toList.length) h,
        fun h => congrArg repeatedWord h⟩
    simp [Finsupp.single_apply, he]
  rw [add_comm, (Commute.one_right (var () : Trunc Unit k)).add_pow, map_sum]
  simp only [one_pow, mul_one, ← nsmul_eq_mul', map_nsmul, hc]
  rw [Finset.sum_eq_single d]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-! ## The Artin action -/

private def leftStrand {n : ℕ} (i : Fin (n - 1)) : Fin n := ⟨i, by have := i.isLt; omega⟩
private def rightStrand {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

private theorem left_ne_right {n : ℕ} (i : Fin (n - 1)) : leftStrand i ≠ rightStrand i := by
  intro h
  have := congrArg Fin.val h
  simp [leftStrand, rightStrand] at this

private def twistMap {ι : Type} [DecidableEq ι] (a b : ι) :
    FreeGroup ι →* FreeGroup ι :=
  FreeGroup.lift fun i =>
    if i = a then FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹
    else if i = b then FreeGroup.of a else FreeGroup.of i

private def twistInv {ι : Type} [DecidableEq ι] (a b : ι) :
    FreeGroup ι →* FreeGroup ι :=
  FreeGroup.lift fun i =>
    if i = a then FreeGroup.of b
    else if i = b then (FreeGroup.of b)⁻¹ * FreeGroup.of a * FreeGroup.of b else FreeGroup.of i

private def twist {ι : Type} [DecidableEq ι] {a b : ι} (h : a ≠ b) :
    MulAut (FreeGroup ι) :=
  { twistMap a b with
    invFun := twistInv a b
    left_inv := by
      have key : (twistInv a b).comp (twistMap a b) = MonoidHom.id _ := by
        apply FreeGroup.ext_hom
        intro i
        rcases eq_or_ne i a with rfl | hia
        · simp [twistMap, twistInv, h.symm, mul_assoc]
        rcases eq_or_ne i b with rfl | hib
        · simp [twistMap, twistInv, h.symm]
        · simp [twistMap, twistInv, hia, hib]
      exact DFunLike.congr_fun key
    right_inv := by
      have key : (twistMap a b).comp (twistInv a b) = MonoidHom.id _ := by
        apply FreeGroup.ext_hom
        intro i
        rcases eq_or_ne i a with rfl | hia
        · simp [twistMap, twistInv, h.symm]
        rcases eq_or_ne i b with rfl | hib
        · simp [twistMap, twistInv, h.symm, mul_assoc]
        · simp [twistMap, twistInv, hia, hib]
      exact DFunLike.congr_fun key }

private theorem twist_apply_of {ι : Type} [DecidableEq ι] {a b : ι} (h : a ≠ b) (i : ι) :
    twist h (FreeGroup.of i) =
      if i = a then FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹
      else if i = b then FreeGroup.of a else FreeGroup.of i :=
  FreeGroup.lift_apply_of

private theorem twist_braid {ι : Type} [DecidableEq ι] {a b c : ι}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    twist hab * (twist hbc * twist hab) = twist hbc * (twist hab * twist hbc) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro i
  simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, twist_apply_of]
  rcases eq_or_ne i a with rfl | hia
  · simp [twist_apply_of, hab, hab.symm, hbc.symm, hac, hac.symm]
    group
  rcases eq_or_ne i b with rfl | hib
  · simp [twist_apply_of, hab, hab.symm, hbc.symm, hac, hac.symm, mul_assoc]
  rcases eq_or_ne i c with rfl | hic
  · simp [twist_apply_of, hab, hab.symm, hbc.symm, hac, hac.symm]
  · simp [twist_apply_of, hia, hib, hic]

private theorem twist_commute {ι : Type} [DecidableEq ι] {a b c d : ι}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : twist hab * twist hcd = twist hcd * twist hab := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro i
  simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, twist_apply_of]
  rcases eq_or_ne i a with rfl | hia
  · simp [twist_apply_of, hac, had, hbc, hbd]
  rcases eq_or_ne i b with rfl | hib
  · simp [twist_apply_of, hab.symm, hac, had, hbc, hbd]
  rcases eq_or_ne i c with rfl | hic
  · simp [twist_apply_of, hac.symm, had.symm, hbc.symm, hbd.symm]
  rcases eq_or_ne i d with rfl | hid
  · simp [twist_apply_of, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
  · simp [twist_apply_of, hia, hib, hic, hid]

private theorem braidRelation {n : ℕ} {G : Type} [Group G]
    (gen : Fin (n - 1) → G)
    (adj : ∀ i j : Fin (n - 1), i.val + 1 = j.val →
      gen i * (gen j * gen i) = gen j * (gen i * gen j))
    (dis : ∀ i j : Fin (n - 1), i ≠ j → i.val + 1 ≠ j.val → j.val + 1 ≠ i.val →
      gen i * gen j = gen j * gen i) :
    ∀ r ∈ (CoxeterMatrix.A (n - 1)).artinRelationsSet, FreeGroup.lift gen r = 1 := by
  rintro r ⟨i, j, hij, _, rfl⟩
  rw [CoxeterMatrix.artinRelation, map_mul, map_inv, mul_inv_eq_one,
    CoxeterMatrix.map_alternatingWord, CoxeterMatrix.map_alternatingWord,
    FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
  change _ = CoxeterMatrix.alternatingWord _ _
    (if i = j then 1 else if j.val + 1 = i.val ∨ i.val + 1 = j.val then 3 else 2)
  have hm : (CoxeterMatrix.A (n - 1)) i j =
      if i = j then 1 else if j.val + 1 = i.val ∨ i.val + 1 = j.val then 3 else 2 := rfl
  rw [hm, ite_eq_right hij]
  split_ifs with h
  · rcases h with h | h
    · simpa [CoxeterMatrix.alternatingWord] using (adj j i h).symm
    · simpa [CoxeterMatrix.alternatingWord] using adj i j h
  · simpa [CoxeterMatrix.alternatingWord] using
      dis i j hij (fun hi => h (Or.inr hi)) (fun hj => h (Or.inl hj))

private def artinAction (n : ℕ) :
    (CoxeterMatrix.A (n - 1)).ArtinGroup →* MulAut (FreeGroup (Fin n)) :=
  PresentedGroup.toGroup <| braidRelation (fun i => twist (left_ne_right i))
    (by
      intro i j h
      have he : rightStrand i = leftStrand j := Fin.ext h
      have hl : leftStrand i ≠ rightStrand j := by
        intro hh
        have := congrArg Fin.val hh
        simp only [leftStrand, rightStrand] at this
        omega
      have h' : leftStrand j ≠ rightStrand j := left_ne_right j
      rw [← he] at h'
      simpa only [he] using twist_braid (left_ne_right i) h' hl)
    (by
      intro i j hij hij' hji'
      apply twist_commute
      · exact fun h => hij (Fin.ext (congrArg (fun u : Fin n => u.val) h))
      · exact fun h => hji' (congrArg Fin.val h).symm
      · exact fun h => hij' (congrArg Fin.val h)
      · intro h
        apply hij
        apply Fin.ext
        have := congrArg Fin.val h
        simp only [rightStrand] at this
        omega)


private theorem prod_adjacent {G : Type} [Monoid G] :
    ∀ {n i : ℕ} (hi : i + 1 < n) (f g : Fin n → G),
      (∀ j : Fin n, j.val ≠ i → j.val ≠ i + 1 → f j = g j) →
      f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩ = g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩ →
      (List.ofFn f).prod = (List.ofFn g).prod := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi f g hfg hp
    cases i with
    | zero =>
      cases n with
      | zero => omega
      | succ n =>
        simp only [List.ofFn_succ, List.prod_cons, ← mul_assoc]
        change f 0 * f (Fin.succ 0) = g 0 * g (Fin.succ 0) at hp
        rw [hp]
        congr 1
        congr 1
        apply congrArg List.ofFn
        funext j
        apply hfg <;> simp
    | succ i =>
      simp only [List.ofFn_succ, List.prod_cons]
      congr 1
      · exact hfg 0 (by simp) (by simp)
      · apply ih (i := i) (show i + 1 < n by omega)
        · intro j hj hj'
          apply hfg <;> simp [Fin.val_succ, *]
        · exact hp

private def boundary (n : ℕ) : FreeGroup (Fin n) :=
  (List.ofFn FreeGroup.of).prod

private theorem twist_boundary {n : ℕ} (i : Fin (n - 1)) :
    twist (left_ne_right i) (boundary n) = boundary n := by
  unfold boundary
  rw [map_list_prod, List.map_ofFn]
  apply prod_adjacent (i := i.val) (rightStrand i).isLt
  · intro j hja hjb
    have hja' : j ≠ leftStrand i := fun h => hja (congrArg Fin.val h)
    have hjb' : j ≠ rightStrand i := fun h => hjb (congrArg Fin.val h)
    simp [twist_apply_of, hja', hjb']
  · have hn := left_ne_right i
    change twist hn (FreeGroup.of (leftStrand i)) *
      twist hn (FreeGroup.of (rightStrand i)) =
        FreeGroup.of (leftStrand i) * FreeGroup.of (rightStrand i)
    simp [twist_apply_of, hn.symm, mul_assoc]

private def braidedFree (n : ℕ) : Subgroup (MulAut (FreeGroup (Fin n))) where
  carrier := { f | f (boundary n) = boundary n ∧ ∃ p : Equiv.Perm (Fin n),
    ∀ i, ∃ w : FreeGroup (Fin n), f (FreeGroup.of i) = w * FreeGroup.of (p i) * w⁻¹ }
  one_mem' := by
    refine ⟨rfl, 1, fun i => ⟨1, ?_⟩⟩
    simp
  mul_mem' := by
    rintro f g ⟨hf, p, hp⟩ ⟨hg, q, hq⟩
    refine ⟨by change f (g (boundary n)) = _; rw [hg, hf], p * q, fun i => ?_⟩
    obtain ⟨w, hw⟩ := hq i
    obtain ⟨v, hv⟩ := hp (q i)
    refine ⟨f w * v, ?_⟩
    change f (g (FreeGroup.of i)) = _
    rw [hw, map_mul, map_mul, map_inv, hv, Equiv.Perm.mul_apply]
    group
  inv_mem' := by
    rintro f ⟨hf, p, hp⟩
    refine ⟨f.injective (by simpa using hf.symm), p⁻¹, fun i => ?_⟩
    obtain ⟨w, hw⟩ := hp (p⁻¹ i)
    change f (FreeGroup.of (p.symm i)) = _ at hw
    rw [show p (p⁻¹ i) = i from p.apply_symm_apply i] at hw
    refine ⟨f.symm w⁻¹, f.injective ?_⟩
    simp only [MulAut.inv_apply, MulEquiv.apply_symm_apply, map_mul, map_inv, inv_inv]
    change FreeGroup.of i = w⁻¹ * f (FreeGroup.of (p.symm i)) * w
    rw [hw]
    group

private theorem artinAction_mem (n : ℕ) (x : (CoxeterMatrix.A (n - 1)).ArtinGroup) :
    artinAction n x ∈ braidedFree n := by
  change x ∈ (braidedFree n).comap (artinAction n)
  apply PresentedGroup.generated_by
  intro i
  change artinAction n (PresentedGroup.of i) ∈ braidedFree n
  have he : artinAction n (PresentedGroup.of i) = twist (left_ne_right i) :=
    PresentedGroup.toGroup.of _
  rw [he]
  have h := left_ne_right i
  refine ⟨twist_boundary i, Equiv.swap (leftStrand i) (rightStrand i), ?_⟩
  intro j
  rcases eq_or_ne j (leftStrand i) with rfl | hjl
  · exact ⟨FreeGroup.of (leftStrand i), by simp [twist_apply_of]⟩
  rcases eq_or_ne j (rightStrand i) with rfl | hjr
  · exact ⟨1, by simp [twist_apply_of, h.symm]⟩
  · exact ⟨1, by simp [twist_apply_of, Equiv.swap_apply_of_ne_of_ne hjl hjr, hjl, hjr]⟩


/-! ## Torsion in the image -/

private def braidRep (n : ℕ) : BraidGroup n →* RingAut (Trunc (Fin n) (n + 1)) :=
  (magnusAut (n + 1)).comp (artinAction n)

private def conjugatedVar {ι : Type} {k : ℕ} (w : FreeGroup ι) (i : ι) : Trunc ι k :=
  ((magnus (k := k) w) * varUnit i * (magnus (k := k) w)⁻¹).val - 1

private theorem map_conjugatedVar {ι : Type} {k : ℕ} {R : Type} [Ring R]
    (F : Trunc ι k →+* R) (w : FreeGroup ι) (i : ι) :
    F (conjugatedVar w i) =
      F (magnus (k := k) w).val * F (var i) * F ((magnus (k := k) w)⁻¹).val := by
  let u : (Trunc ι k)ˣ := magnus w
  change F ((u * varUnit i * u⁻¹).val - 1) = _
  rw [map_sub, map_one, Units.val_mul, Units.val_mul, coe_varUnit, mul_add, mul_one, add_mul,
    Units.mul_inv, map_add, map_one, add_sub_cancel_left, map_mul,
    map_mul]

private theorem map_conjugatedVar_zero {ι : Type} {k : ℕ} {R : Type} [Ring R]
    (F : Trunc ι k →+* R) (w : FreeGroup ι) (i : ι) (h : F (var i) = 0) :
    F (conjugatedVar w i) = 0 := by
  simp [map_conjugatedVar, h]

private theorem map_conjugatedVar_scalar {ι : Type} {k : ℕ}
    (F : Trunc ι k →+* Trunc Unit k) (w : FreeGroup ι) (i : ι) :
    F (conjugatedVar w i) = F (var i) := by
  rw [map_conjugatedVar, scalar_comm _ (F (var i)), mul_assoc, ← map_mul,
    Units.mul_inv, map_one, mul_one]

private theorem conjugacy_pow {ι : Type} (F : MulAut (FreeGroup ι)) (p : Equiv.Perm ι)
    (h : ∀ i, ∃ w, F (FreeGroup.of i) = w * FreeGroup.of (p i) * w⁻¹) :
    ∀ (m : ℕ) i, ∃ w, (F ^ m) (FreeGroup.of i) = w * FreeGroup.of ((p ^ m) i) * w⁻¹ := by
  intro m
  induction m with
  | zero => intro i; exact ⟨1, by simp⟩
  | succ m ih =>
    intro i
    obtain ⟨w, hw⟩ := ih i
    obtain ⟨v, hv⟩ := h ((p ^ m) i)
    refine ⟨F w * v, ?_⟩
    simp only [pow_succ', Equiv.Perm.mul_apply, MulAut.mul_apply, hw, map_inv, map_mul, hv]
    group

private theorem braidRep_pow_var {n : ℕ} (x : BraidGroup n) (p : Equiv.Perm (Fin n))
    (h : ∀ i, ∃ w, artinAction n x (FreeGroup.of i) = w * FreeGroup.of (p i) * w⁻¹)
    (m : ℕ) (i : Fin n) : ∃ w, (braidRep n x ^ m) (var i) =
      conjugatedVar w ((p ^ m) i) := by
  obtain ⟨w, hw⟩ := conjugacy_pow _ p h m i
  refine ⟨w, ?_⟩
  rw [braidRep, MonoidHom.comp_apply, ← map_pow]
  change liftMagnus ((artinAction n x) ^ m) (var i) = _
  rw [liftMagnus_var, hw, map_mul, map_mul, map_inv]
  rw [conjugatedVar, show magnus (FreeGroup.of ((p ^ m) i)) = varUnit (k := n + 1) ((p ^ m) i) from
    FreeGroup.lift_apply_of]

private def boundaryVal (n : ℕ) : Trunc (Fin n) (n + 1) :=
  (magnus (k := n + 1) (boundary n)).val

private theorem boundaryVal_eq (n : ℕ) :
    boundaryVal n = (List.ofFn fun i : Fin n => (1 + var i)).prod := by
  change ((Units.coeHom _).comp magnus) (boundary n) = _
  simp [boundary, map_list_prod, List.map_ofFn, magnus, coe_varUnit, Function.comp_def]

private theorem braidRep_fix_boundary {n : ℕ} (x : BraidGroup n) :
    braidRep n x (boundaryVal n) = boundaryVal n := by
  have hx := (artinAction_mem _ x).1
  have he := liftMagnus_natural (k := n + 1) (artinAction n x) (boundary n)
  rw [hx] at he
  exact congrArg Units.val he

private theorem prod_select {α M : Type} [Monoid M] (s : Set α) [DecidablePred (· ∈ s)]
    (u : M) (l : List α) :
    (l.map fun i => if i ∈ s then u else 1).prod = u ^ (l.filter fun i => i ∈ s).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a ∈ s
    · simp [h, ih, pow_succ']
    · simp [h, ih]

private theorem braidRep_prime_order {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (x : BraidGroup n)
    (hx : braidRep n x ^ p = 1) : braidRep n x = 1 := by
  classical
  let F := braidRep n x
  obtain ⟨_, π, hπ⟩ := artinAction_mem n x
  have hvars (m : ℕ) (i : Fin n) : ∃ w, (F ^ m) (var i) =
      conjugatedVar w ((π ^ m) i) := braidRep_pow_var x π hπ m i
  have hlin (m : ℕ) (i : Fin n) : level 2 ((F ^ m) (var i) - var ((π ^ m) i)) := by
    obtain ⟨w, hw⟩ := hvars m i
    rw [hw]
    exact conjugate_var_diff _ _
  have hπp : π ^ p = 1 := by
    apply Equiv.ext
    intro i
    have hi := hlin p i
    change F ^ p = 1 at hx
    rw [hx, RingAut.one_apply, var_sub_level_two_iff (by omega)] at hi
    exact hi.symm
  by_cases hid : π = 1
  · refine triangular_no_torsion (F := F) (fun i => ?_) hp.pos hx
    simpa [hid] using hlin 1 i
  exfalso
  obtain ⟨a, ha⟩ : ∃ a, π a ≠ a := by
    by_contra! h
    exact hid (Equiv.ext h)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have ha_period : Function.IsPeriodicPt π p a := by
    change (π ^ p) a = a
    rw [hπp, Equiv.Perm.one_apply]
  have ha_minimal : Function.minimalPeriod π a = p :=
    (Function.minimalPeriod_eq_prime_iff).2 ⟨ha_period, ha⟩
  let e : Fin p ↪ Fin n :=
    ⟨fun i => (π ^ i.val) a, fun {i j} h => by
      apply Fin.ext
      apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := ⇑π) (x := a)
        (ha_minimal.symm ▸ i.isLt) (ha_minimal.symm ▸ j.isLt)).mp
      exact h⟩
  have hpn : p ≤ n := by simpa using Fintype.card_le_of_injective e e.injective
  have hpk : p < n + 1 := by omega
  let rot : Equiv.Perm (Fin p) := Equiv.addRight 1
  have hrot (j : Fin p) : e (rot j) = π (e j) := by
    change (π ^ (j + 1).val) a = π ((π ^ j.val) a)
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hp.one_lt]
    rw [show ((π ^ ((j.val + 1) % p)) a) = (π ^ (j.val + 1)) a from
      ha_period.iterate_mod_apply _, pow_succ', Equiv.Perm.mul_apply]
  have hrot_iter (m : ℕ) : (rot^[m] 0).val = m % p := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      change ((rot^[m] 0).val + 1 % p) % p = _
      rw [ih, Nat.mod_add_mod, Nat.add_mod_mod]
  have hfw (j : Fin p) : (F ^ (rot j).val) (var a) = F ((F ^ j.val) (var a)) := by
    rw [show (rot j).val = (j.val + 1) % p by
      simp [rot, Fin.val_add, Nat.mod_eq_of_lt hp.one_lt]]
    have hperiod (z : Trunc (Fin n) (n + 1)) : Function.IsPeriodicPt F p z := by
      change F^[p] z = z
      rw [← RingAut.coe_pow, hx]
      rfl
    rw [show (F ^ ((j.val + 1) % p)) (var a) = (F ^ (j.val + 1)) (var a) by
      simp only [RingAut.coe_pow]; exact (hperiod _).iterate_mod_apply _,
      pow_succ', RingAut.mul_apply]
  let prev : Fin n → Fin p := Function.invFun e
  have hprev (j : Fin p) : prev (e j) = j := Function.leftInverse_invFun e.injective j
  let P : Trunc (Fin n) (n + 1) →+* Trunc (Fin p) (n + 1) :=
    subst (fun i => if i ∈ Set.range e then var (prev i) else 0) fun i => by
      split_ifs
      · exact var_level _
      · exact level_zero
  have hP (i : Fin n) : P (var i) = if i ∈ Set.range e then var (prev i) else 0 :=
    subst_var _ _ _
  -- Replace the variables on the orbit by the successive images of one variable.
  let C : Fin n → Trunc (Fin n) (n + 1) :=
    fun i => if i ∈ Set.range e then (F ^ (prev i).val) (var a) else var i
  have hC (j : Fin p) : C (e j) = (F ^ j.val) (var a) := by
    simp [C, hprev]
  have hClin (i : Fin n) : level 2 (C i - var i) := by
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      rw [hC]
      exact hlin j.val a
    · rw [show C i = var i from ite_eq_right hi, sub_self]; exact level_zero
  have hCpos (i : Fin n) : level 1 (C i) := by
    simpa using level_add (level_mono (by decide : 1 ≤ 2) (hClin i)) (var_level i)
  let T := subst C hCpos
  let θ := RingEquiv.ofBijective T (triangular_bijective T (fun i => by
    rw [subst_var]; exact hClin i))
  have hθ (i : Fin n) : θ (var i) = C i := subst_var C hCpos i
  let Q := P.comp θ.symm.toRingHom
  have hQ (i : Fin n) (hi : i ∉ Set.range e) : Q (var i) = 0 := by
    have hh : θ (var i) = var i := by rw [hθ]; exact ite_eq_right hi
    change P (θ.symm (var i)) = 0
    rw [← hh, θ.symm_apply_apply, hP, ite_eq_right hi]
  have hQT (i : Fin n) : Q (θ (var i)) = P (var i) := by
    change P (θ.symm (θ (var i))) = _
    rw [θ.symm_apply_apply]
  have hPOrbit (j : Fin p) : P (var (e j)) = var j := by
    rw [hP, ite_eq_left (Set.mem_range_self j), hprev]
  -- In these coordinates, deleting the other variables intertwines the action and rotation.
  have hQF : Q.comp F.toRingHom = (relabel rot).comp Q := by
    apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := θ.surjective z
    have hh : ((Q.comp F.toRingHom).comp θ.toRingHom) =
        (((relabel rot).comp Q).comp θ.toRingHom) := by
      apply hom_ext
      intro i
      change Q (F (θ (var i))) = relabel rot (Q (θ (var i)))
      rw [hQT]
      by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        rw [hθ, hC, ← hfw, ← hC, ← hθ, hQT, hPOrbit, hPOrbit, relabel_var]
      · have hπi : π i ∉ Set.range e := by
          rintro ⟨j, hj⟩
          obtain ⟨j, rfl⟩ := rot.surjective j
          exact hi ⟨j, π.injective ((hrot j).symm.trans hj)⟩
        obtain ⟨w, hw⟩ := hvars 1 i
        rw [hθ, show C i = var i by exact ite_eq_right hi,
          show F (var i) = conjugatedVar w (π i) by simpa using hw, hP, ite_eq_right hi,
          map_zero]
        exact map_conjugatedVar_zero Q w (π i) (hQ _ hπi)
    exact DFunLike.congr_fun hh z
  -- This coordinate change preserves commutative specialization because it uses conjugates.
  have hSc : (scalar.comp P).comp θ.toRingHom = scalar.comp P := by
    apply hom_ext
    intro i
    change scalar (P (θ (var i))) = scalar (P (var i))
    rw [hθ]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      obtain ⟨w, hw⟩ := hvars j.val a
      rw [hC, show e j = (π ^ j.val) a by rfl, hw]
      exact map_conjugatedVar_scalar (scalar.comp P) w _
    · rw [show C i = var i by exact ite_eq_right hi]
  have hScQ (z : Trunc (Fin n) (n + 1)) : scalar (Q z) = scalar (P z) := by
    have h := DFunLike.congr_fun hSc (θ.symm z)
    change scalar (P (θ (θ.symm z))) = scalar (Q z) at h
    simpa using h.symm
  -- Rotation makes the sums of coefficients for the different first letters equal.
  let y := Q (boundaryVal n)
  have hy : relabel rot y = y := by
    have he := DFunLike.congr_fun hQF (boundaryVal n)
    change Q (F (boundaryVal n)) = relabel rot y at he
    rw [braidRep_fix_boundary x] at he
    exact he.symm
  have hconst (i : Fin p) :
      headCoeff hpk (rot i) y = headCoeff hpk i y := by
    simpa only [hy] using headCoeff_relabel hpk rot i y
  have hh (i : Fin p) : headCoeff hpk i y = headCoeff hpk 0 y := by
    have hi : rot^[i.val] 0 = i := Fin.ext (by rw [hrot_iter, Nat.mod_eq_of_lt i.isLt])
    rw [← hi]
    generalize i.val = m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', hconst, ih]
  have hdiv : repeatedCoeff hpk (scalar y) = (p : ℤ) * headCoeff hpk 0 y := by
    rw [scalar_coeff_sum hpk hp.pos]
    simp_rw [hh, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Specializing the boundary instead gives (1 + X)^p, with top coefficient one.
  have hscalar : scalar (P (boundaryVal n)) = (1 + var () : Trunc Unit (n + 1)) ^ p := by
    rw [boundaryVal_eq, ← RingHom.comp_apply, map_list_prod, List.map_ofFn, List.ofFn_eq_map]
    change ((List.finRange n).map (fun i => scalar (P (1 + var i)))).prod = _
    have hterm (i : Fin n) :
        scalar (P (1 + var i)) = if i ∈ Set.range e then 1 + var () else 1 := by
      rw [map_add, map_one, map_add, map_one, hP]
      split_ifs <;> simp [relabel_var]
    simp only [hterm]
    rw [prod_select]
    congr 1
    let l := (List.finRange n).filter fun i => i ∈ Set.range e
    have hnd : l.Nodup := (List.nodup_finRange n).filter _
    have he : l.toFinset = Finset.univ.map e := by
      ext i
      simp [l, Set.mem_range]
    change l.length = p
    simpa only [he, Finset.card_map, Finset.card_univ, Fintype.card_fin] using
      (List.toFinset_card_of_nodup hnd).symm
  rw [show scalar y = scalar (P (boundaryVal n)) from hScQ _, hscalar, scalar_coeff_pow] at hdiv
  have hd : (p : ℤ) ∣ 1 := ⟨_, hdiv⟩
  have hnat : p ∣ 1 := by exact_mod_cast hd
  exact hp.ne_one (Nat.dvd_one.mp hnat)

/-! ## A nontrivial element in the kernel -/

private theorem braidRep_preserves_level {n d : ℕ} (x : BraidGroup n) {z : Trunc (Fin n) (n + 1)}
    (hz : level d z) : level d (braidRep n x z) :=
  subst_level (fun _ => magnus_level _) hz

private def shifts {ι : Type} {k : ℕ} (f : RingAut (Trunc ι k)) (e : ℕ) : Prop :=
  ∀ d z, level d z → level (d + e) (f z - z)

private theorem commutator_shifts {ι : Type} {k e f : ℕ} {A B : RingAut (Trunc ι k)}
    (hA : shifts A e) (hB : shifts B f)
    (hAi : ∀ d z, level d z → level d (A⁻¹ z))
    (hBi : ∀ d z, level d z → level d (B⁻¹ z)) :
    shifts ⁅A, B⁆ (e + f) := by
  intro d z hz
  let y := A⁻¹ (B⁻¹ z)
  have hy : level d y := hAi _ _ (hBi _ _ hz)
  have hyz : B (A y) = z := by simp [y]
  rw [commutatorElement_def]
  change level _ (A (B y) - z)
  rw [← hyz, show A (B y) - B (A y) =
      (A (B y - y) - (B y - y)) - (B (A y - y) - (A y - y)) by
    simp only [map_sub]; abel]
  apply level_sub
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA _ _ (hB _ _ hy)
  · simpa only [Nat.add_assoc] using hB _ _ (hA _ _ hy)

private def iteratedCommutator {G : Type} [Group G] (a b : G) : ℕ → G
  | 0 => b
  | m + 1 => ⁅a, iteratedCommutator a b m⁆

private theorem map_iteratedCommutator {G H : Type} [Group G] [Group H] (φ : G →* H)
    (a b : G) (m : ℕ) :
    φ (iteratedCommutator a b m) = iteratedCommutator (φ a) (φ b) m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [iteratedCommutator, commutatorElement_def, ih]

private theorem twist_sq_apply_of {ι : Type} [DecidableEq ι] {a b : ι} (h : a ≠ b) (i : ι) :
    (twist h ^ 2) (FreeGroup.of i) =
      if i = a ∨ i = b then
        (FreeGroup.of a * FreeGroup.of b) * FreeGroup.of i * (FreeGroup.of a * FreeGroup.of b)⁻¹
      else FreeGroup.of i := by
  rcases eq_or_ne i a with rfl | hia
  · simp [pow_two, MulAut.mul_apply, twist_apply_of, h.symm]
    group
  rcases eq_or_ne i b with rfl | hib
  · simp [pow_two, MulAut.mul_apply, twist_apply_of, h.symm]
  · simp [pow_two, MulAut.mul_apply, twist_apply_of, hia, hib]

private def generator {n : ℕ} (i : Fin (n - 1)) : BraidGroup n :=
  CoxeterMatrix.ArtinGroup.of (CoxeterMatrix.A (n - 1)) i

private theorem artinAction_generator {n : ℕ} (i : Fin (n - 1)) :
    artinAction n (generator i) = twist (left_ne_right i) :=
  PresentedGroup.toGroup.of _

private theorem generator_sq_shifts {n : ℕ} (i : Fin (n - 1)) :
    shifts (braidRep n (generator i ^ 2)) 1 := by
  have hlin (j : Fin n) : level 2 (braidRep n (generator i ^ 2) (var j) - var j) := by
    change level 2 (liftMagnus (artinAction n (generator i ^ 2)) (var j) - var j)
    rw [map_pow, artinAction_generator, liftMagnus_var, twist_sq_apply_of]
    split_ifs
    · let w := FreeGroup.of (leftStrand i) * FreeGroup.of (rightStrand i)
      change level 2 ((magnus (k := n + 1) (w * FreeGroup.of j * w⁻¹)).val - 1 - var j)
      rw [map_mul, map_mul, map_inv, magnus_apply_of]
      exact conjugate_var_diff _ _
    · simp only [magnus_apply_of, coe_varUnit, add_sub_cancel_left, sub_self]
      exact level_zero
  intro d z hz
  exact delta_shift (F := (braidRep n (generator i ^ 2)).toRingHom) hlin hz

private theorem iteratedCommutator_mem_ker {n : ℕ} (i j : Fin (n - 1)) :
    iteratedCommutator (generator i ^ 2) (generator j ^ 2) n ∈ (braidRep n).ker := by
  let a := generator i ^ 2
  let b := generator j ^ 2
  have hs (m : ℕ) : shifts (braidRep n (iteratedCommutator a b m)) (m + 1) := by
    induction m with
    | zero => exact generator_sq_shifts j
    | succ m ih =>
      rw [iteratedCommutator, map_commutatorElement]
      have hA (d : ℕ) (z : Trunc (Fin n) (n + 1)) (hz : level d z) :
          level d ((braidRep n a)⁻¹ z) := by
        rw [← map_inv]
        exact braidRep_preserves_level _ hz
      have hB (d : ℕ) (z : Trunc (Fin n) (n + 1)) (hz : level d z) :
          level d ((braidRep n (iteratedCommutator a b m))⁻¹ z) := by
        rw [← map_inv]
        exact braidRep_preserves_level _ hz
      simpa only [Nat.add_left_comm] using commutator_shifts (generator_sq_shifts i) ih hA hB
  apply MonoidHom.mem_ker.mpr
  apply RingEquiv.ext
  intro z
  exact sub_eq_zero.mp (level_eq_zero (by simp) (hs n 0 z (level_univ z)))

private def intertwines {G H : Type} [Group G] [Group H]
    (f : G →* H) (u : MulAut G) (v : MulAut H) : Prop :=
  ∀ z, f (u z) = v (f z)

private theorem intertwines_mul {G H : Type} [Group G] [Group H]
    {f : G →* H} {u u' : MulAut G} {v v' : MulAut H}
    (h : intertwines f u v) (h' : intertwines f u' v') :
    intertwines f (u * u') (v * v') := fun z => (h _).trans (congrArg v (h' z))

private theorem intertwines_inv {G H : Type} [Group G] [Group H]
    {f : G →* H} {u : MulAut G} {v : MulAut H}
    (h : intertwines f u v) : intertwines f u⁻¹ v⁻¹ := by
  intro z
  apply v.injective
  simpa using (h (u.symm z)).symm

private theorem intertwines_iteratedCommutator {G H : Type} [Group G] [Group H]
    {f : G →* H} {u u' : MulAut G} {v v' : MulAut H}
    (h : intertwines f u v) (h' : intertwines f u' v') (m : ℕ) :
    intertwines f (iteratedCommutator u u' m) (iteratedCommutator v v' m) := by
  induction m with
  | zero => exact h'
  | succ m ih =>
    rw [iteratedCommutator, iteratedCommutator, commutatorElement_def, commutatorElement_def]
    exact intertwines_mul (intertwines_mul (intertwines_mul h ih) (intertwines_inv h))
      (intertwines_inv ih)

private abbrev freeX : FreeGroup Bool := FreeGroup.of true
private abbrev freeY : FreeGroup Bool := FreeGroup.of false

private theorem free_iteratedCommutator_ne_one (m : ℕ) :
    iteratedCommutator freeX⁻¹ freeY⁻¹ m ≠ 1 := by
  let χ : FreeGroup Bool →* Multiplicative ℤ :=
    FreeGroup.lift fun b => Multiplicative.ofAdd (if b then 1 else 0)
  have hx : χ freeX = Multiplicative.ofAdd 1 := FreeGroup.lift_apply_of
  have hy : χ freeY = 1 := FreeGroup.lift_apply_of
  have hχ (m : ℕ) : χ (iteratedCommutator freeX⁻¹ freeY⁻¹ m) = 1 := by
    cases m with
    | zero => simp [iteratedCommutator, hy]
    | succ m =>
      rw [iteratedCommutator, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (Commute.all ..)
  induction m with
  | zero => simp [iteratedCommutator]
  | succ m ih =>
    intro he
    rw [iteratedCommutator, commutatorElement_eq_one_iff_commute, Commute.inv_left_iff] at he
    obtain ⟨k, hk⟩ := FreeGroup.commute_of_iff.mp he
    change freeX ^ k = iteratedCommutator freeX⁻¹ freeY⁻¹ m at hk
    have h0 : (Multiplicative.ofAdd (1 : ℤ)) ^ k = 1 := by
      rw [← hx, ← map_zpow, hk, hχ]
    have hk0 : k = 0 := by
      have h := congrArg Multiplicative.toAdd h0
      simpa using h
    exact ih (by simpa [hk0] using hk.symm)

private def evaluateThree (n : ℕ) : FreeGroup (Fin n) →* FreeGroup Bool :=
  FreeGroup.lift fun i =>
    if i.val = 0 then freeY else if i.val = 1 then freeY⁻¹ * freeX⁻¹
    else if i.val = 2 then freeX else 1

private theorem evaluateThree_of {n : ℕ} (i : Fin n) :
    evaluateThree n (FreeGroup.of i) =
      if i.val = 0 then freeY else if i.val = 1 then freeY⁻¹ * freeX⁻¹
      else if i.val = 2 then freeX else 1 := FreeGroup.lift_apply_of

private theorem evaluateThree_surjective {n : ℕ} (hn : 3 ≤ n) :
    Function.Surjective (evaluateThree n) := by
  -- The images of the first and third generators give a section.
  let s : FreeGroup Bool →* FreeGroup (Fin n) :=
    FreeGroup.lift fun b => FreeGroup.of (if b then ⟨2, by omega⟩ else ⟨0, by omega⟩)
  have he : (evaluateThree n).comp s = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro b
    change evaluateThree n (s (FreeGroup.of b)) = _
    rw [show s (FreeGroup.of b) =
      FreeGroup.of (if b then ⟨2, by omega⟩ else ⟨0, by omega⟩) from FreeGroup.lift_apply_of]
    cases b <;> simp [evaluateThree_of]
  exact Function.RightInverse.surjective (DFunLike.congr_fun he)

private theorem evaluateThree_intertwines {n : ℕ} (i : Fin (n - 1))
    (hi : i.val < 2) :
    intertwines (evaluateThree n) (artinAction n (generator i ^ 2))
      (MulAut.conj (if i.val = 0 then freeX⁻¹ else freeY⁻¹)) := by
  rw [map_pow, artinAction_generator]
  have he : (evaluateThree n).comp (twist (left_ne_right i) ^ 2).toMonoidHom =
      (MulAut.conj (if i.val = 0 then freeX⁻¹ else freeY⁻¹)).toMonoidHom.comp
        (evaluateThree n) := by
    apply FreeGroup.ext_hom
    intro j
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, twist_sq_apply_of, MulAut.conj_apply]
    simp only [Fin.ext_iff, leftStrand, rightStrand]
    have hival : i.val = 0 ∨ i.val = 1 := by omega
    rcases hival with hi0 | hi1
    · by_cases hj0 : j.val = 0
      · simp [hi0, hj0, evaluateThree_of]
      by_cases hj1 : j.val = 1
      · simp [hi0, hj1, evaluateThree_of]
      by_cases hj2 : j.val = 2
      · simp [hi0, hj2, evaluateThree_of]
      · simp [hi0, hj0, hj1, hj2, evaluateThree_of]
    · by_cases hj0 : j.val = 0
      · simp [hi1, hj0, evaluateThree_of]
      by_cases hj1 : j.val = 1
      · simp [hi1, hj1, evaluateThree_of]
      by_cases hj2 : j.val = 2
      · simp [hi1, hj2, evaluateThree_of]
      · simp [hi1, hj0, hj1, hj2, evaluateThree_of]
  exact DFunLike.congr_fun he

private theorem iterated_braid_ne_one {n : ℕ} (hn : 3 ≤ n) (m : ℕ) :
    iteratedCommutator (generator (⟨0, by omega⟩ : Fin (n - 1)) ^ 2)
      (generator (⟨1, by omega⟩ : Fin (n - 1)) ^ 2) m ≠ 1 := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  let j : Fin (n - 1) := ⟨1, by omega⟩
  let a := generator i ^ 2
  let b := generator j ^ 2
  let c := iteratedCommutator freeX⁻¹ freeY⁻¹ m
  change iteratedCommutator a b m ≠ 1
  intro hm
  have ha : intertwines (evaluateThree n) (artinAction n a) (MulAut.conj freeX⁻¹) :=
    evaluateThree_intertwines i (show 0 < 2 by decide)
  have hb : intertwines (evaluateThree n) (artinAction n b) (MulAut.conj freeY⁻¹) :=
    evaluateThree_intertwines j (show 1 < 2 by decide)
  have hi := intertwines_iteratedCommutator ha hb m
  rw [← map_iteratedCommutator, ← map_iteratedCommutator, hm, map_one] at hi
  have hcenter : c ∈ Subgroup.center (FreeGroup Bool) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := evaluateThree_surjective hn y
    have he := hi z
    change evaluateThree n z = c * evaluateThree n z * c⁻¹ at he
    exact (eq_mul_inv_iff_mul_eq.mp he)
  rw [FreeGroup.center_eq_bot_of_nontrivial, Subgroup.mem_bot] at hcenter
  exact free_iteratedCommutator_ne_one m hcenter

/-! ## The quotient and its properties -/

private theorem braidRep_torsion {n : ℕ} (hn : 1 ≤ n) (b : BraidGroup n)
    (h : IsOfFinOrder (braidRep n b)) : braidRep n b = 1 := by
  by_contra hb
  have ho : orderOf (braidRep n b) ≠ 1 := fun h => hb (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd ho
  let k := orderOf (braidRep n b) / p
  have horder : orderOf (braidRep n (b ^ k)) = p := by
    rw [map_pow]
    exact orderOf_pow_orderOf_div h.orderOf_pos.ne' hpd
  have hpow := (orderOf_eq_prime_iff (hp := ⟨hp⟩)).mp horder
  exact hpow.2 (braidRep_prime_order hn hp (b ^ k) hpow.1)

private theorem generator_linear {n : ℕ} (i : Fin (n - 1)) (j : Fin n) :
    level 2 (braidRep n (generator i) (var j) -
      var (Equiv.swap (leftStrand i) (rightStrand i) j)) := by
  have ht := left_ne_right i
  change level 2 (liftMagnus (artinAction n (generator i)) (var j) - _)
  rw [artinAction_generator, liftMagnus_var, twist_apply_of, Equiv.swap_apply_def]
  split_ifs with ha hb
  · simp only [map_mul, map_inv]
    rw [show magnus (FreeGroup.of (rightStrand i)) = varUnit (k := n + 1) (rightStrand i) from
       FreeGroup.lift_apply_of]
    exact conjugate_var_diff _ _
  all_goals
    rw [show magnus (FreeGroup.of _) = varUnit (k := n + 1) _ from FreeGroup.lift_apply_of,
      coe_varUnit]
    simpa using level_zero

private theorem braidRep_noncommute {n : ℕ} (hn : 3 ≤ n) :
    ∃ a b : BraidGroup n, braidRep n a * braidRep n b ≠ braidRep n b * braidRep n a := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  let j : Fin (n - 1) := ⟨1, by omega⟩
  let l : Fin n := ⟨0, by omega⟩
  let m : Fin n := ⟨1, by omega⟩
  let r : Fin n := ⟨2, by omega⟩
  let A := braidRep n (generator i)
  let B := braidRep n (generator j)
  refine ⟨generator i, generator j, ?_⟩
  change A * B ≠ B * A
  have hlm : l ≠ m := by intro h; have := congrArg Fin.val h; contradiction
  have hlr : l ≠ r := by intro h; have := congrArg Fin.val h; contradiction
  have hmr : m ≠ r := by
    intro h
    have he : (1 : ℕ) = 2 := congrArg Fin.val h
    omega
  have hA : level 2 (A (var l) - var m) := by
    simpa only [show leftStrand i = l by rfl, show rightStrand i = m by rfl,
      Equiv.swap_apply_left] using generator_linear i l
  have hB : level 2 (B (var l) - var l) := by
    simpa only [show leftStrand j = m by rfl, show rightStrand j = r by rfl,
      Equiv.swap_apply_of_ne_of_ne hlm hlr] using generator_linear j l
  have hB' : level 2 (B (var m) - var r) := by
    simpa only [show leftStrand j = m by rfl, show rightStrand j = r by rfl,
      Equiv.swap_apply_left] using generator_linear j m
  have hab : level 2 ((A * B) (var l) - var m) := by
    have he := braidRep_preserves_level (generator i) hB
    change level 2 (A (B (var l) - var l)) at he
    rw [map_sub] at he
    simpa using level_add he hA
  have hba : level 2 ((B * A) (var l) - var r) := by
    have he := braidRep_preserves_level (generator j) hA
    change level 2 (B (A (var l) - var m)) at he
    rw [map_sub] at he
    simpa using level_add he hB'
  intro he
  rw [he] at hab
  have hd : level 2 (var (k := n + 1) m - var r) := by
    have h := level_sub hba hab
    rwa [show (B * A) (var l) - var r - ((B * A) (var l) - var m) = var m - var r by abel] at h
  exact hmr ((var_sub_level_two_iff (by omega) m r).mp hd)

end

@[expose] public section

/--
**Braid groups on three or more strands have proper non-abelian torsion-free quotients.** For
every $n \ge 3$, the braid group $B_n$ on $n$ strands has a nontrivial normal subgroup $N$ such that
the quotient $B_n / N$ is non-abelian and torsion-free (no element other than the identity has
finite order). For $n > 4$ this answers Kourovka Notebook Problem 14.102(c).

Source: Direct construction: $N$ is the kernel of Artin's action of $B_n$ on the free group of rank
$n$, read through the Magnus expansion modulo the words of length greater than $n$. The case
$n > 4$ is Problem 14.102(c) of E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026).
-/
theorem exists_torsionFree_nonabelian_proper_quotient (n : ℕ) (hn : 3 ≤ n) :
    ∃ (N : Subgroup (BraidGroup n)) (_ : N.Normal), N ≠ ⊥ ∧
      (∃ x y : BraidGroup n ⧸ N, x * y ≠ y * x) ∧
      ∀ x : BraidGroup n ⧸ N, x ≠ 1 → ¬ IsOfFinOrder x := by
  let φ := braidRep n
  refine ⟨φ.ker, inferInstance, ?_, ?_, ?_⟩
  · intro he
    let i : Fin (n - 1) := ⟨0, by omega⟩
    let j : Fin (n - 1) := ⟨1, by omega⟩
    have hi := iteratedCommutator_mem_ker i j
    change _ ∈ φ.ker at hi
    rw [he, Subgroup.mem_bot] at hi
    exact iterated_braid_ne_one hn n hi
  · obtain ⟨a, b, h⟩ := braidRep_noncommute hn
    refine ⟨a, b, fun he => h ?_⟩
    simpa only [map_mul, QuotientGroup.kerLift_mk] using
      congrArg (QuotientGroup.kerLift φ) he
  · intro a ha h
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
    have hb := (QuotientGroup.kerLift φ).isOfFinOrder h
    rw [QuotientGroup.kerLift_mk] at hb
    apply ha (QuotientGroup.kerLift_injective φ _)
    rw [QuotientGroup.kerLift_mk, map_one]
    exact braidRep_torsion (by omega) b hb

/--
**Braid groups on five or more strands have proper non-abelian torsion-free quotients.** For
every $n > 4$, the braid group $B_n$ on $n$ strands has a nontrivial normal subgroup $N$ such that
the quotient $B_n / N$ is non-abelian and torsion-free (no element other than the identity has
finite order).

The Kourovka Archive answers 14.102(c) "Yes, it does", citing Linnell and Schick (every braid group
is residually torsion-free nilpotent-by-finite); Humphries had constructed such quotients for
$n < 7$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 14.102 (V. Lin; V. Shpilrain). Part (c)
is in the Archive of Solved Problems, answered "Yes" citing P. Linnell and T. Schick, J. Amer.
Math. Soc. 20 (2007), no. 4, 1003-1051 (every braid group is residually torsion-free
nilpotent-by-finite), with a comment of 2001 citing S. P. Humphries, Int. J. Algebra Comput. 11
(2001), no. 3, 363-373 (n < 7). Parts (a) and (b) are solved in the main list: (a) F. Castel,
Geometric representations of the braid groups, Astérisque 378 (2016) (n ≥ 6), and L. Chen,
K. Kordek and D. Margalit, Homomorphisms between braid groups, arXiv:1910.00712 (n = 5); (b)
S. Orevkov, Ann. Fac. Sci. Toulouse Math. 33 (2024), no. 1, 105-121, extending K. Kordek and
D. Margalit, Bull. London Math. Soc. 54 (2022), 95-111 (n ≥ 7).
-/
theorem braidTorsionFreeNonabelianProperQuotient_holds :
    braidTorsionFreeNonabelianProperQuotient := by
  intro n hn
  exact exists_torsionFree_nonabelian_proper_quotient n (by omega)

end

end MathlibExt.GroupTheory.BraidGroupEndomorphismsKourovka14Problem102Wanted
