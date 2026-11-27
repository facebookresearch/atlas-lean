/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Ring

/-!
# Endomorphisms determined by their values at two elements (Kourovka Notebook Problem 13.66)

Kourovka Notebook, Archive of Solved Problems, Problem 13.66 (V. E. Shpil'rain): let `F` be a (a)
free, (b) free metabelian group of finite rank, and `M` the set of endomorphisms of `F` with
non-cyclic images. Can one choose `g, h ∈ F` such that `φ, ψ ∈ M`, `φ(g) = ψ(g)` and `φ(h) = ψ(h)`
imply `φ = ψ`?

The main result here is the refutation for free metabelian groups:
`freeMetabelianEndomorphismsDeterminedByTwoElements_refuted` says that for some finite rank, no
two elements determine the endomorphisms with non-cyclic images. The proof works in rank three:
two endomorphisms factoring through the abelianization, a rank-two linear map and two commuting
commutators agree on any two prescribed elements, have non-cyclic ranges, and differ.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted

open scoped commutatorElement

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.66 (V. E.
Shpil'rain). UnsolvedMath record UM-00700984 (`KOU-13.66`), dataset ulamai/UnsolvedMath v1.8.0.

Ranks `n` are arbitrary finite; for `n ≤ 1` every image is cyclic, so (a) is vacuous there. (a) is
stated for every rank; (b) is stated for every rank and refuted, which says that for some finite
rank no such pair exists ("not always"). The free metabelian group of rank `n` is `F_n / F_n''`.
-/

@[ext]
private structure Heisenberg where
  a : ℤ
  b : ℤ
  c : ℤ

private instance : Mul Heisenberg where
  mul x y := ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩

private instance : One Heisenberg where
  one := ⟨0, 0, 0⟩

private instance : Inv Heisenberg where
  inv x := ⟨-x.a, -x.b, -x.c + x.a * x.b⟩

@[simp]
private lemma mul_mk (a b c a' b' c' : ℤ) :
    (⟨a, b, c⟩ : Heisenberg) * ⟨a', b', c'⟩ = ⟨a + a', b + b', c + c' + a * b'⟩ :=
  rfl

@[simp]
private lemma one_mk : (1 : Heisenberg) = ⟨0, 0, 0⟩ := rfl

@[simp]
private lemma inv_mk (a b c : ℤ) : (⟨a, b, c⟩ : Heisenberg)⁻¹ = ⟨-a, -b, -c + a * b⟩ :=
  rfl

private instance : Group Heisenberg where
  mul_assoc x y z := by
    obtain ⟨a, b, c⟩ := x; obtain ⟨a', b', c'⟩ := y; obtain ⟨a'', b'', c''⟩ := z
    ext <;> simp only [mul_mk] <;> ring
  one_mul x := by obtain ⟨a, b, c⟩ := x; ext <;> simp
  mul_one x := by obtain ⟨a, b, c⟩ := x; ext <;> simp
  inv_mul_cancel x := by obtain ⟨a, b, c⟩ := x; ext <;> simp

private lemma mul_a (x y : Heisenberg) : (x * y).a = x.a + y.a := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨a', b', c'⟩ := y; rfl

private lemma mul_b (x y : Heisenberg) : (x * y).b = x.b + y.b := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨a', b', c'⟩ := y; rfl

private lemma mul_c (x y : Heisenberg) : (x * y).c = x.c + y.c + x.a * y.b := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨a', b', c'⟩ := y; rfl

private lemma inv_a (x : Heisenberg) : x⁻¹.a = -x.a := by
  obtain ⟨a, b, c⟩ := x; rfl

private lemma inv_b (x : Heisenberg) : x⁻¹.b = -x.b := by
  obtain ⟨a, b, c⟩ := x; rfl

private lemma inv_c (x : Heisenberg) : x⁻¹.c = -x.c + x.a * x.b := by
  obtain ⟨a, b, c⟩ := x; rfl

/-- The abelianization of the Heisenberg group, recording the first two coordinates. -/
private def heisAB : Heisenberg →* Multiplicative (ℤ × ℤ) where
  toFun x := Multiplicative.ofAdd (x.a, x.b)
  map_one' := rfl
  map_mul' x y := by rw [mul_a, mul_b]; rfl

private lemma heisenberg_commutator (x y : Heisenberg) :
    ⁅x, y⁆ = ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  ext <;> simp [commutatorElement_def, mul_a, mul_b, mul_c, inv_a, inv_b, inv_c]
  ring

private lemma heisenberg_derivedSeries_two :
    Subgroup.derivedSeries Heisenberg 2 = ⊥ := by
  rw [Subgroup.derivedSeries_succ, Subgroup.derivedSeries_succ,
    Subgroup.derivedSeries_zero]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hcomm : _root_.commutator Heisenberg ≤ heisAB.ker := by
    change ⁅(⊤ : Subgroup Heisenberg), ⊤⁆ ≤ heisAB.ker
    rw [Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, heisenberg_commutator]
    rfl
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hx0 : x.a = 0 ∧ x.b = 0 := by
    have h := hcomm hx
    rw [MonoidHom.mem_ker] at h
    have h2 : (x.a, x.b) = (0, 0) := by
      have h3 := congrArg Multiplicative.toAdd h
      simpa [heisAB] using h3
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  have hy0 : y.a = 0 ∧ y.b = 0 := by
    have h := hcomm hy
    rw [MonoidHom.mem_ker] at h
    have h2 : (y.a, y.b) = (0, 0) := by
      have h3 := congrArg Multiplicative.toAdd h
      simpa [heisAB] using h3
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
  have hxy : y * x = x * y := by
    ext
    · simp [mul_a, hx0.1, hy0.1]
    · simp [mul_b, hx0.2, hy0.2]
    · simp [mul_c, hx0.1, hx0.2, hy0.1, hy0.2, add_comm]
  exact hxy

/-- **The free metabelian group $M_n$.** For a natural number $n$, the free metabelian group of
rank $n$ is the quotient $F_n / F_n''$ of the free group $F_n$ on $n$ generators by its second
derived subgroup $F_n'' = [F_n', F_n']$, where $F_n' = [F_n, F_n]$ is the derived subgroup of
$F_n$. -/
abbrev FreeMetabelianGroup (n : ℕ) : Type :=
  FreeGroup (Fin n) ⧸ Subgroup.derivedSeries (FreeGroup (Fin n)) 2

/-- The free metabelian group of rank three, the rank used in the refutation. -/
private abbrev MetabelianThree : Type := FreeMetabelianGroup 3

private def gen (i : Fin 3) : MetabelianThree :=
  QuotientGroup.mk' (Subgroup.derivedSeries (FreeGroup (Fin 3)) 2) (FreeGroup.of i)

private def abG : FreeGroup (Fin 3) →* Multiplicative (Fin 3 → ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (Pi.single i 1)

private lemma abG_apply (i : Fin 3) :
    abG (FreeGroup.of i) = Multiplicative.ofAdd (Pi.single i 1) := by
  simp [abG]

private lemma abG_ker : Subgroup.derivedSeries (FreeGroup (Fin 3)) 2 ≤ abG.ker := by
  refine (Subgroup.derivedSeries_antitone (G := FreeGroup (Fin 3))
    (by norm_num : (1 : ℕ) ≤ 2)).trans ?_
  change _root_.commutator (FreeGroup (Fin 3)) ≤ abG.ker
  change ⁅(⊤ : Subgroup (FreeGroup (Fin 3))), ⊤⁆ ≤ abG.ker
  rw [Subgroup.commutator_le]
  intro u _ v _
  rw [MonoidHom.mem_ker, map_commutatorElement]
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

private def ab : MetabelianThree →* Multiplicative (Fin 3 → ℤ) :=
  QuotientGroup.lift _ abG abG_ker

private lemma ab_gen (i : Fin 3) : ab (gen i) = Multiplicative.ofAdd (Pi.single i 1) :=
  (QuotientGroup.lift_mk _ abG_ker (FreeGroup.of i)).trans (abG_apply i)

/-- Heisenberg maps: send two chosen generators to the two noncentral coordinates. -/
private def heisG (p q : Fin 3) : FreeGroup (Fin 3) →* Heisenberg :=
  FreeGroup.lift fun i => if i = p then ⟨1, 0, 0⟩ else if i = q then ⟨0, 1, 0⟩ else 1

private lemma heisG_ker (p q : Fin 3) :
    Subgroup.derivedSeries (FreeGroup (Fin 3)) 2 ≤ (heisG p q).ker := by
  refine (Subgroup.derivedSeries (FreeGroup (Fin 3)) 2).map_eq_bot_iff.mp ?_
  exact le_bot_iff.mp ((Subgroup.map_derivedSeries_le_derivedSeries (heisG p q) 2).trans
    (le_of_eq heisenberg_derivedSeries_two))

private def heisM (p q : Fin 3) : MetabelianThree →* Heisenberg :=
  QuotientGroup.lift _ (heisG p q) (heisG_ker p q)

private lemma heisM_gen (p q i : Fin 3) :
    heisM p q (gen i) = heisG p q (FreeGroup.of i) :=
  QuotientGroup.lift_mk _ (heisG_ker p q) (FreeGroup.of i)

private lemma heisG_of (p q i : Fin 3) :
    heisG p q (FreeGroup.of i) = if i = p then ⟨1, 0, 0⟩ else if i = q then ⟨0, 1, 0⟩ else 1 := by
  simp [heisG]

private lemma derivedSeries_MetabelianThree_two :
    Subgroup.derivedSeries MetabelianThree 2 = ⊥ := by
  have h := Subgroup.map_derivedSeries_eq (QuotientGroup.mk'_surjective
    (Subgroup.derivedSeries (FreeGroup (Fin 3)) 2)) (f := QuotientGroup.mk'
    (Subgroup.derivedSeries (FreeGroup (Fin 3)) 2)) 2
  rw [← h]
  refine (Subgroup.derivedSeries (FreeGroup (Fin 3)) 2).map_eq_bot_iff.mpr ?_
  exact le_of_eq (QuotientGroup.ker_mk' _).symm

private lemma commute_c1_c2 :
    Commute ⁅gen 0, gen 1⁆ ⁅gen 0, gen 2⁆ := by
  have h1 : ⁅gen 0, gen 1⁆ ∈ _root_.commutator MetabelianThree := by
    change ⁅gen 0, gen 1⁆ ∈ ⁅(⊤ : Subgroup MetabelianThree), ⊤⁆
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h2 : ⁅gen 0, gen 2⁆ ∈ _root_.commutator MetabelianThree := by
    change ⁅gen 0, gen 2⁆ ∈ ⁅(⊤ : Subgroup MetabelianThree), ⊤⁆
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hmem : ⁅⁅gen 0, gen 1⁆, ⁅gen 0, gen 2⁆⁆ ∈
      ⁅_root_.commutator MetabelianThree, _root_.commutator MetabelianThree⁆ :=
    Subgroup.commutator_mem_commutator h1 h2
  have hbot : ⁅_root_.commutator MetabelianThree, _root_.commutator MetabelianThree⁆ = ⊥ := by
    rw [← Subgroup.derivedSeries_one, ← Subgroup.derivedSeries_succ,
      derivedSeries_MetabelianThree_two]
  rw [hbot] at hmem
  have : ⁅⁅gen 0, gen 1⁆, ⁅gen 0, gen 2⁆⁆ = 1 := Subgroup.mem_bot.mp hmem
  exact commutatorElement_eq_one_iff_commute.mp this

/-- The central subgroup of the Heisenberg group, as a homomorphism. -/
private def centralHom : Multiplicative ℤ →* Heisenberg where
  toFun z := ⟨0, 0, Multiplicative.toAdd z⟩
  map_one' := rfl
  map_mul' x y := by
    ext <;> simp [toAdd_mul]

/-- Powers of the central Heisenberg element. -/
private lemma central_zpow (n : ℤ) : (⟨0, 0, 1⟩ : Heisenberg) ^ n = ⟨0, 0, n⟩ := by
  have h1 : centralHom (Multiplicative.ofAdd (1 : ℤ)) = (⟨0, 0, 1⟩ : Heisenberg) := rfl
  have h2 : (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
    rw [← ofAdd_zsmul]
    simp
  calc (⟨0, 0, 1⟩ : Heisenberg) ^ n = centralHom ((Multiplicative.ofAdd (1 : ℤ)) ^ n) := by
        rw [← h1, map_zpow]
    _ = centralHom (Multiplicative.ofAdd n) := by rw [h2]
    _ = ⟨0, 0, n⟩ := rfl

private def alphaHom : Multiplicative (Fin 2 → ℤ) →* MetabelianThree where
  toFun z := ⁅gen 0, gen 1⁆ ^ (Multiplicative.toAdd z 0) *
    ⁅gen 0, gen 2⁆ ^ (Multiplicative.toAdd z 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add]
    exact Commute.mul_mul_mul_comm (Commute.zpow_zpow commute_c1_c2 _ _) _ _

private lemma alphaHom_apply (z : Multiplicative (Fin 2 → ℤ)) :
    alphaHom z = ⁅gen 0, gen 1⁆ ^ (Multiplicative.toAdd z 0) *
      ⁅gen 0, gen 2⁆ ^ (Multiplicative.toAdd z 1) :=
  rfl

private lemma heisM_c1 : heisM 0 1 ⁅gen 0, gen 1⁆ = ⟨0, 0, 1⟩ := by
  simp [map_commutatorElement, heisM_gen, heisG_of, heisenberg_commutator]

private lemma heisM_c2 : heisM 0 1 ⁅gen 0, gen 2⁆ = 1 := by
  have h : heisM 0 1 ⁅gen 0, gen 2⁆ = ⁅(⟨1, 0, 0⟩ : Heisenberg), 1⁆ := by
    simp [map_commutatorElement, heisM_gen, heisG_of]
  rw [h, commutatorElement_one_right]

private lemma heisM_c1' : heisM 0 2 ⁅gen 0, gen 1⁆ = 1 := by
  have h : heisM 0 2 ⁅gen 0, gen 1⁆ = ⁅(⟨1, 0, 0⟩ : Heisenberg), 1⁆ := by
    simp [map_commutatorElement, heisM_gen, heisG_of]
  rw [h, commutatorElement_one_right]

private lemma heisM_c2' : heisM 0 2 ⁅gen 0, gen 2⁆ = ⟨0, 0, 1⟩ := by
  simp [map_commutatorElement, heisM_gen, heisG_of, heisenberg_commutator]

private lemma alphaHom_injective : Function.Injective alphaHom := by
  intro x y hxy
  have h1 : alphaHom (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have key1 : (heisM 0 1) (alphaHom (x * y⁻¹)) =
      ⟨0, 0, Multiplicative.toAdd (x * y⁻¹) 0⟩ := by
    rw [alphaHom_apply, map_mul, map_zpow, map_zpow, heisM_c1, heisM_c2, central_zpow,
      one_zpow, mul_one]
  have key2 : (heisM 0 2) (alphaHom (x * y⁻¹)) =
      ⟨0, 0, Multiplicative.toAdd (x * y⁻¹) 1⟩ := by
    rw [alphaHom_apply, map_mul, map_zpow, map_zpow, heisM_c1', heisM_c2', one_zpow,
      central_zpow, one_mul]
  rw [h1, map_one] at key1 key2
  have hu0 : Multiplicative.toAdd (x * y⁻¹) 0 = 0 := by
    have h := congrArg Heisenberg.c key1
    simpa using h.symm
  have hu1 : Multiplicative.toAdd (x * y⁻¹) 1 = 0 := by
    have h := congrArg Heisenberg.c key2
    simpa using h.symm
  have hu : Multiplicative.toAdd (x * y⁻¹) = 0 := by
    funext i
    fin_cases i <;> simp [hu0, hu1]
  have hxy1 : x * y⁻¹ = 1 := by
    have h2 : Multiplicative.toAdd (x * y⁻¹) =
        Multiplicative.toAdd (1 : Multiplicative (Fin 2 → ℤ)) := by
      rw [hu]
      rfl
    exact Multiplicative.toAdd.injective h2
  exact (mul_inv_eq_one).mp hxy1

/-- The dot product of two vectors in `ℤ ^ 3`, written out in coordinates. -/
private def dot3 (a z : Fin 3 → ℤ) : ℤ := a 0 * z 0 + a 1 * z 1 + a 2 * z 2

/-- The cross product of two vectors in `ℤ ^ 3`. -/
private def cross3 (u v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

private lemma dot_cross3_left (u v : Fin 3 → ℤ) : dot3 (cross3 u v) u = 0 := by
  simp [dot3, cross3]
  ring

private lemma dot_cross3_right (u v : Fin 3 → ℤ) : dot3 (cross3 u v) v = 0 := by
  simp [dot3, cross3]
  ring

private lemma cross3_neg (u v : Fin 3 → ℤ) : cross3 v u = -cross3 u v := by
  funext i
  fin_cases i <;> simp [cross3, Pi.neg_apply] <;> ring

private lemma find_orthogonal (v w : Fin 3 → ℤ) (hvw : cross3 v w = 0) (hv : v ≠ 0) :
    ∃ a : Fin 3 → ℤ, a ≠ 0 ∧ dot3 a v = 0 ∧ dot3 a w = 0 := by
  have e0 : v 1 * w 2 = v 2 * w 1 := by
    have h0 := congrFun hvw 0
    have h : v 1 * w 2 - v 2 * w 1 = 0 := by simpa [cross3] using h0
    exact sub_eq_zero.mp h
  have e1 : v 2 * w 0 = v 0 * w 2 := by
    have h0 := congrFun hvw 1
    have h : v 2 * w 0 - v 0 * w 2 = 0 := by simpa [cross3] using h0
    exact sub_eq_zero.mp h
  have e2 : v 0 * w 1 = v 1 * w 0 := by
    have h0 := congrFun hvw 2
    have h : v 0 * w 1 - v 1 * w 0 = 0 := by simpa [cross3] using h0
    exact sub_eq_zero.mp h
  by_cases h0 : cross3 v (Pi.single 0 (1 : ℤ)) ≠ 0
  · refine ⟨cross3 v (Pi.single 0 (1 : ℤ)), h0, dot_cross3_left _ _, ?_⟩
    simp [dot3, cross3, Pi.single]
    omega
  · by_cases h1 : cross3 v (Pi.single 1 (1 : ℤ)) ≠ 0
    · refine ⟨cross3 v (Pi.single 1 (1 : ℤ)), h1, dot_cross3_left _ _, ?_⟩
      simp [dot3, cross3, Pi.single]
      omega
    · by_cases h2 : cross3 v (Pi.single 2 (1 : ℤ)) ≠ 0
      · refine ⟨cross3 v (Pi.single 2 (1 : ℤ)), h2, dot_cross3_left _ _, ?_⟩
        simp [dot3, cross3, Pi.single]
        omega
      · exfalso
        apply hv
        have h0' : cross3 v (Pi.single 0 (1 : ℤ)) = 0 := not_not.mp h0
        have h1' : cross3 v (Pi.single 1 (1 : ℤ)) = 0 := not_not.mp h1
        have h2' : cross3 v (Pi.single 2 (1 : ℤ)) = 0 := not_not.mp h2
        have c0 := congrFun h0' 1
        have c0' := congrFun h0' 2
        have c1 := congrFun h1' 0
        have c1' := congrFun h1' 2
        simp [cross3, Pi.single] at c0 c0' c1 c1'
        funext i
        fin_cases i <;> simp_all

private lemma exists_orthogonal (v w : Fin 3 → ℤ) :
    ∃ a : Fin 3 → ℤ, a ≠ 0 ∧ dot3 a v = 0 ∧ dot3 a w = 0 := by
  by_cases hvw : cross3 v w ≠ 0
  · exact ⟨cross3 v w, hvw, dot_cross3_left _ _, dot_cross3_right _ _⟩
  · have hvw' : cross3 v w = 0 := not_not.mp hvw
    by_cases hv : v ≠ 0
    · exact find_orthogonal v w hvw' hv
    · have hv' : v = 0 := not_not.mp hv
      by_cases hw : w ≠ 0
      · obtain ⟨a, ha0, haw, hav⟩ := find_orthogonal w v (by rw [cross3_neg, hvw']; simp) hw
        exact ⟨a, ha0, hav, haw⟩
      · have hw' : w = 0 := not_not.mp hw
        refine ⟨Pi.single 0 (1 : ℤ), by simp, by simp [dot3, hv'], by simp [dot3, hw']⟩

private def qFun (a b z : Fin 3 → ℤ) : Fin 2 → ℤ := ![dot3 a z, dot3 b z]

private def qAdd (a b : Fin 3 → ℤ) : (Fin 3 → ℤ) →+ (Fin 2 → ℤ) where
  toFun z := qFun a b z
  map_zero' := by
    ext j
    fin_cases j <;> simp [qFun, dot3]
  map_add' x y := by
    ext j
    fin_cases j <;> simp [qFun, dot3, Pi.add_apply] <;> ring

private def qHom (a b : Fin 3 → ℤ) :
    Multiplicative (Fin 3 → ℤ) →* Multiplicative (Fin 2 → ℤ) :=
  (qAdd a b).toMultiplicative

private def linAdd (f : (Fin 2 → ℤ) → (Fin 2 → ℤ)) (hf : ∀ x y, f (x + y) = f x + f y) :
    (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  AddMonoidHom.mk' f hf

private def linHom (f : (Fin 2 → ℤ) → (Fin 2 → ℤ)) (hf : ∀ x y, f (x + y) = f x + f y) :
    Multiplicative (Fin 2 → ℤ) →* Multiplicative (Fin 2 → ℤ) :=
  (linAdd f hf).toMultiplicative

example (a b z : Fin 3 → ℤ) :
    qHom a b (Multiplicative.ofAdd z) = Multiplicative.ofAdd (qFun a b z) := by
  simp [qHom, qAdd]

example (f : (Fin 2 → ℤ) → (Fin 2 → ℤ)) (hf : ∀ x y, f (x + y) = f x + f y)
    (z : Fin 2 → ℤ) :
    linHom f hf (Multiplicative.ofAdd z) = Multiplicative.ofAdd (f z) := by
  simp [linHom, linAdd]

private lemma dot3_single_left (j : Fin 3) (z : Fin 3 → ℤ) :
    dot3 (Pi.single j (1 : ℤ)) z = z j := by
  fin_cases j <;> simp [dot3, Pi.single]

private lemma dot3_single_right (i : Fin 3) (a : Fin 3 → ℤ) :
    dot3 a (Pi.single i (1 : ℤ)) = a i := by
  fin_cases i <;> simp [dot3, Pi.single]

private lemma qHom_apply_ab (a b : Fin 3 → ℤ) (m : MetabelianThree) :
    qHom a b (ab m) = Multiplicative.ofAdd (qFun a b (Multiplicative.toAdd (ab m))) := by
  simp [qHom, qAdd]

private lemma linHom_apply (f : (Fin 2 → ℤ) → (Fin 2 → ℤ))
    (hf : ∀ x y, f (x + y) = f x + f y) (z : Multiplicative (Fin 2 → ℤ)) :
    linHom f hf z = Multiplicative.ofAdd (f (Multiplicative.toAdd z)) := by
  simp [linHom, linAdd]

private def endoOf (a b : Fin 3 → ℤ) (f : (Fin 2 → ℤ) → (Fin 2 → ℤ))
    (hf : ∀ x y, f (x + y) = f x + f y) : MetabelianThree →* MetabelianThree :=
  alphaHom.comp ((linHom f hf).comp ((qHom a b).comp ab))

private lemma endoOf_apply (a b : Fin 3 → ℤ) (f : (Fin 2 → ℤ) → (Fin 2 → ℤ))
    (hf : ∀ x y, f (x + y) = f x + f y) (m : MetabelianThree) :
    endoOf a b f hf m =
      alphaHom (Multiplicative.ofAdd (f (qFun a b (Multiplicative.toAdd (ab m))))) := by
  change alphaHom (((linHom f hf).comp ((qHom a b).comp ab)) m) = _
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, qHom_apply_ab, linHom_apply]
  simp

private lemma endoOf_apply_exp (a b : Fin 3 → ℤ) (f : (Fin 2 → ℤ) → (Fin 2 → ℤ))
    (hf : ∀ x y, f (x + y) = f x + f y) (m : MetabelianThree) :
    endoOf a b f hf m =
      ⁅gen 0, gen 1⁆ ^ (f (qFun a b (Multiplicative.toAdd (ab m))) 0) *
        ⁅gen 0, gen 2⁆ ^ (f (qFun a b (Multiplicative.toAdd (ab m))) 1) := by
  rw [endoOf_apply, alphaHom_apply]
  simp

private lemma not_cyclic_of_gen (E : MetabelianThree →* MetabelianThree)
    (a : Fin 3 → ℤ) (i j : Fin 3)
    (K : ℤ) (hK : K ≠ 0) (hi : a i ≠ 0)
    (hEi : E (gen i) = ⁅gen 0, gen 1⁆ ^ (K * a i))
    (hEj : E (gen j) = ⁅gen 0, gen 1⁆ ^ (K * a j) * ⁅gen 0, gen 2⁆ ^ 1)
    (hE : ∀ m : MetabelianThree, ∃ u : Fin 2 → ℤ, E m = alphaHom (Multiplicative.ofAdd u)) :
    ¬ IsCyclic E.range := by
  intro hCyc
  obtain ⟨d, hd⟩ := IsCyclic.exists_generator (α := E.range)
  have hdmem : (d : MetabelianThree) ∈ E.range := d.2
  obtain ⟨m0, hm0⟩ := hdmem
  obtain ⟨u, hu⟩ := hE m0
  have hd_eq : (d : MetabelianThree) = alphaHom (Multiplicative.ofAdd u) := by rw [← hm0, hu]
  have hpi : (⟨E (gen i), ⟨gen i, rfl⟩⟩ : E.range) ∈ Subgroup.zpowers d := hd _
  have hpj : (⟨E (gen j), ⟨gen j, rfl⟩⟩ : E.range) ∈ Subgroup.zpowers d := hd _
  rw [Subgroup.mem_zpowers_iff] at hpi hpj
  obtain ⟨r, hr⟩ := hpi
  obtain ⟨s, hs⟩ := hpj
  have hri : (d : MetabelianThree) ^ r = E (gen i) := by
    have h := congrArg (fun x : E.range => (x : MetabelianThree)) hr
    simpa using h
  have hsj : (d : MetabelianThree) ^ s = E (gen j) := by
    have h := congrArg (fun x : E.range => (x : MetabelianThree)) hs
    simpa using h
  have keyi : r • u = ![K * a i, 0] := by
    have h1 : alphaHom (Multiplicative.ofAdd (r • u)) = ⁅gen 0, gen 1⁆ ^ (K * a i) := by
      have hpow : (alphaHom (Multiplicative.ofAdd u)) ^ r =
          alphaHom (Multiplicative.ofAdd (r • u)) := by
        rw [← map_zpow, ofAdd_zsmul]
      rw [← hpow, ← hd_eq, hri, hEi]
    have h2 : alphaHom (Multiplicative.ofAdd (r • u)) =
        alphaHom (Multiplicative.ofAdd ![K * a i, 0]) := by
      rw [h1]
      simp [alphaHom_apply]
    have h3 := alphaHom_injective h2
    have h4 := congrArg Multiplicative.toAdd h3
    simpa using h4
  have keyj : s • u = ![K * a j, 1] := by
    have h1 : alphaHom (Multiplicative.ofAdd (s • u)) =
        ⁅gen 0, gen 1⁆ ^ (K * a j) * ⁅gen 0, gen 2⁆ ^ 1 := by
      have hpow : (alphaHom (Multiplicative.ofAdd u)) ^ s =
          alphaHom (Multiplicative.ofAdd (s • u)) := by
        rw [← map_zpow, ofAdd_zsmul]
      rw [← hpow, ← hd_eq, hsj, hEj]
    have h2 : alphaHom (Multiplicative.ofAdd (s • u)) =
        alphaHom (Multiplicative.ofAdd ![K * a j, 1]) := by
      rw [h1]
      simp [alphaHom_apply]
    have h3 := alphaHom_injective h2
    have h4 := congrArg Multiplicative.toAdd h3
    simpa using h4
  have h1i : r * u 1 = 0 := by
    have h := congrFun keyi 1
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have h1j : s * u 1 = 1 := by
    have h := congrFun keyj 1
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have hu1 : u 1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h1j
    exact zero_ne_one h1j
  have hr0 : r = 0 := by
    have := (mul_eq_zero.mp h1i).resolve_right hu1
    exact this
  have h0i : r * u 0 = K * a i := by
    have h := congrFun keyi 0
    simpa [Pi.smul_apply, smul_eq_mul] using h
  rw [hr0, zero_mul] at h0i
  exact hK (by
    have : K * a i = 0 := h0i.symm
    exact (mul_eq_zero.mp this).resolve_right hi)

private lemma exists_ne_fin3 (i : Fin 3) : ∃ j : Fin 3, j ≠ i := by
  fin_cases i
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨0, by decide⟩

private lemma keyLemma (g h : MetabelianThree) (a : Fin 3 → ℤ) (i j : Fin 3) (hji : j ≠ i)
    (hi : a i ≠ 0)
    (hav : dot3 a (Multiplicative.toAdd (ab g)) = 0)
    (haw : dot3 a (Multiplicative.toAdd (ab h)) = 0) :
    ∃ φ ψ : MetabelianThree →* MetabelianThree, φ ≠ ψ ∧ ¬ IsCyclic φ.range ∧ ¬ IsCyclic ψ.range ∧
      φ g = ψ g ∧ φ h = ψ h := by
  classical
  set b : Fin 3 → ℤ := Pi.single j (1 : ℤ) with hb
  have hf1 : ∀ x y : Fin 2 → ℤ, id (x + y) = id x + id y := fun _ _ => rfl
  have hf2 : ∀ x y : Fin 2 → ℤ, (fun z => ![2 * z 0, z 1]) (x + y) =
      (fun z => ![2 * z 0, z 1]) x + (fun z => ![2 * z 0, z 1]) y := by
    intro x y
    funext k
    fin_cases k <;> simp [Pi.add_apply]; ring
  have hqgen : ∀ t : Fin 3, qFun a b (Pi.single t (1 : ℤ)) = ![a t, b t] := by
    intro t
    simp [qFun, dot3_single_right]
  have habgen : ∀ t : Fin 3, Multiplicative.toAdd (ab (gen t)) = Pi.single t (1 : ℤ) := by
    intro t
    rw [ab_gen]
    simp
  have hbi : b i = 0 := by
    simp [hb, Pi.single_eq_of_ne (Ne.symm hji)]
  have hbj : b j = 1 := by simp [hb]
  have eval_gen : ∀ (f : (Fin 2 → ℤ) → (Fin 2 → ℤ))
      (hf : ∀ x y, f (x + y) = f x + f y) (t : Fin 3),
      endoOf a b f hf (gen t) =
        ⁅gen 0, gen 1⁆ ^ (f ![a t, b t] 0) * ⁅gen 0, gen 2⁆ ^ (f ![a t, b t] 1) := by
    intro f hf t
    rw [endoOf_apply_exp, habgen, hqgen]
  refine ⟨endoOf a b id hf1, endoOf a b (fun z => ![2 * z 0, z 1]) hf2, ?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hgi := congrFun (congrArg DFunLike.coe hEq) (gen i)
    rw [eval_gen id hf1 i, eval_gen (fun z => ![2 * z 0, z 1]) hf2 i] at hgi
    simp only [id] at hgi
    rw [hbi] at hgi
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_zero, mul_one] at hgi
    have h2a : (2 : ℤ) * a i = a i + a i := by ring
    rw [h2a, zpow_add] at hgi
    have hcan : (1 : MetabelianThree) = ⁅gen 0, gen 1⁆ ^ (a i) := by
      have h' : ⁅gen 0, gen 1⁆ ^ (a i) * (1 : MetabelianThree) =
          ⁅gen 0, gen 1⁆ ^ (a i) * ⁅gen 0, gen 1⁆ ^ (a i) := by
        rw [mul_one]
        exact hgi
      exact mul_left_cancel h'
    have hα : alphaHom (Multiplicative.ofAdd ![a i, 0]) = 1 := by
      simp [alphaHom_apply, hcan.symm]
    have hinj := alphaHom_injective (show alphaHom (Multiplicative.ofAdd ![a i, 0]) =
        alphaHom 1 from by rw [hα, map_one])
    have h0 : ![a i, 0] = (0 : Fin 2 → ℤ) := by
      have h := congrArg Multiplicative.toAdd hinj
      simpa using h
    have h0i : a i = 0 := by
      have h' := congrFun h0 0
      simpa using h'
    exact hi h0i
  · apply not_cyclic_of_gen (endoOf a b id hf1) a i j 1 (by norm_num) hi
    · rw [eval_gen id hf1 i, hbi]
      simp
    · rw [eval_gen id hf1 j, hbj]
      simp
    · intro m
      exact ⟨id (qFun a b (Multiplicative.toAdd (ab m))), endoOf_apply a b id hf1 m⟩
  · apply not_cyclic_of_gen (endoOf a b (fun z => ![2 * z 0, z 1]) hf2) a i j 2 (by norm_num) hi
    · rw [eval_gen (fun z => ![2 * z 0, z 1]) hf2 i, hbi]
      simp
    · rw [eval_gen (fun z => ![2 * z 0, z 1]) hf2 j, hbj]
      simp
    · intro m
      exact ⟨(fun z => ![2 * z 0, z 1]) (qFun a b (Multiplicative.toAdd (ab m))),
        endoOf_apply a b (fun z => ![2 * z 0, z 1]) hf2 m⟩
  · rw [endoOf_apply_exp, endoOf_apply_exp]
    simp [qFun, hav]
  · rw [endoOf_apply_exp, endoOf_apply_exp]
    simp [qFun, haw]

/-- **Groups whose endomorphisms with non-cyclic images are determined by two elements.** A group
$F$ has this property when there exist elements $g, h \in F$ such that any two endomorphisms
$\varphi, \psi$ of $F$ whose images are not cyclic subgroups and which satisfy
$\varphi(g) = \psi(g)$ and $\varphi(h) = \psi(h)$ are equal. -/
def DeterminedByTwoElements (F : Type) [Group F] : Prop :=
  ∃ g h : F, ∀ φ ψ : F →* F, ¬ IsCyclic φ.range → ¬ IsCyclic ψ.range → φ g = ψ g →
    φ h = ψ h → φ = ψ

/-- **Shpil'rain's two-element problem for free groups (Kourovka 13.66(a)).** For every natural
number $n$, the free group $F_n$ of rank $n$ contains two elements $g$ and $h$ such that any two
endomorphisms of $F_n$ whose images are not cyclic subgroups and which agree at $g$ and at $h$
are equal; that is, $F_n$ has its endomorphisms with non-cyclic images determined by two
elements. -/
def freeGroupEndomorphismsDeterminedByTwoElements : Prop :=
  ∀ n : ℕ, DeterminedByTwoElements (FreeGroup (Fin n))

/-- **Shpil'rain's two-element problem for free metabelian groups (Kourovka 13.66(b)).** For every
natural number $n$, the free metabelian group $M_n = F_n / F_n''$ of rank $n$ (the quotient of the
free group $F_n$ of rank $n$ by its second derived subgroup) contains two elements $g$ and $h$
such that any two endomorphisms of $M_n$ whose images are not cyclic subgroups and which agree at
$g$ and at $h$ are equal. -/
def freeMetabelianEndomorphismsDeterminedByTwoElements : Prop :=
  ∀ n : ℕ, DeterminedByTwoElements (FreeMetabelianGroup n)

/--
**Endomorphisms of free metabelian groups are not always determined by two elements.** For a
natural number $n$, let $M_n = F_n / F_n''$ be the free metabelian group of rank $n$, the quotient
of the free group $F_n$ of rank $n$ by its second derived subgroup. There is an $n$ such that for
all elements $g, h \in M_n$ there are endomorphisms $\varphi \ne \psi$ of $M_n$ whose images are
not cyclic subgroups and which satisfy $\varphi(g) = \psi(g)$ and $\varphi(h) = \psi(h)$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 13.66 (V. E. Shpil'rain); resolution: (a) D. Lee, J. Algebra 247 (2002), no. 2,
509-540; (b) E. I. Timoshenko, Math. Notes 62 (1998), no. 5-6, 767-770, Kourovka Archive, Problem
13.66 (answers: a) Yes, one can; b) No, not always).
-/
theorem freeMetabelianEndomorphismsDeterminedByTwoElements_refuted :
    ¬ freeMetabelianEndomorphismsDeterminedByTwoElements := by
  intro hall
  obtain ⟨g, h, hg⟩ := hall 3
  obtain ⟨a, ha0, hav, haw⟩ := exists_orthogonal (Multiplicative.toAdd (ab g))
    (Multiplicative.toAdd (ab h))
  have hne : ∃ i, a i ≠ 0 := by
    by_contra hc
    apply ha0
    funext i
    by_contra hii
    exact hc ⟨i, hii⟩
  obtain ⟨i, hi⟩ := hne
  obtain ⟨j, hji⟩ := exists_ne_fin3 i
  obtain ⟨φ, ψ, hne', hφ, hψ, hφg, hψh⟩ := keyLemma g h a i j hji hi hav haw
  exact hne' (hg φ ψ hφ hψ hφg hψh)

end MathlibExt.GroupTheory.EndomorphismsDeterminedByTwoElementsKourovka13Problem66Wanted
