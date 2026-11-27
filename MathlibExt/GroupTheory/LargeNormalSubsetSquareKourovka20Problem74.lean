/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Large normal subsets whose square is not the whole group (Kourovka Notebook Problem 20.74)

For part (a), Sheinfeld's construction uses matrices with a pointwise fixed two-dimensional
subspace and no eigenvalue `-1`. Counting conjugates of admissible block diagonal matrices gives
a uniform density bound, while the diagonal involution with a one-dimensional fixed space is
missing from the square. Odd-dimensional special linear groups over `ZMod 5` are simple by
Iwasawa's criterion and the triviality of their scalar center.

Source: O. Sheinfeld, *On Shalev's Quantitative Version of Thompson's Conjecture*,
arXiv:2609.22004v1, Theorems 1.6 and 8.2.
-/

namespace MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted

open scoped Pointwise

@[expose] public section

/-- **Large inverse-closed normal subsets with small square.** A group $G$ has this property when it
has a subset $S$ such that $g s g^{-1} \in S$ and $s^{-1} \in S$ for all $g \in G$ and $s \in S$,
$S$ has more than $|G| / \log_2 |G|$ elements, and $S^2 = \{st : s, t \in S\}$ is not all of $G$.

The definition is intended for finite groups $G$. -/
def HasLargeInverseClosedNormalSubsetWithSmallSquare (G : Type) [Group G] : Prop :=
  ∃ S : Set G, (∀ g s : G, s ∈ S → g * s * g⁻¹ ∈ S) ∧ (∀ s ∈ S, s⁻¹ ∈ S) ∧
    (Nat.card G : ℝ) / Real.logb 2 (Nat.card G) < S.ncard ∧ S * S ≠ Set.univ

/-- **Pyber's conjecture for finite simple groups (Kourovka 20.74(a)).** This proposition states
that there is a natural number $N$ such that every nonabelian finite simple group $G$ that has a
subset $S$ closed under conjugation and under inversion with $|S| > |G| / \log_2 |G|$ and
$S^2 \ne G$, where $S^2 = \{st : s, t \in S\}$, has order $|G| \le N$. Since there are only finitely
many groups of each order, this says that only finitely many such groups exist up to isomorphism. -/
def finitelyManySimpleGroupsWithLargeNormalSubset : Prop :=
  ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    HasLargeInverseClosedNormalSubsetWithSmallSquare G → Nat.card G ≤ N

end

section

open Matrix Matrix.SpecialLinearGroup
open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- A determinant-one diagonal supported on two indices is a product of transvections. -/
private theorem sl_diag2n_factor {i j : ι} (hij : i ≠ j) (a : F) (ha : a ≠ 0) :
    diag2n hij a ha =
      SpecialLinearGroup.transvection hij (a - 1) *
      SpecialLinearGroup.transvection hij.symm 1 *
      SpecialLinearGroup.transvection hij (a⁻¹ - 1) *
      SpecialLinearGroup.transvection hij.symm (-a) := by
  apply coeMonoidHom_injective
  simp only [map_mul]
  simp only [coeMonoidHom_apply, diag2n_coe, SpecialLinearGroup.transvection_coe,
    mul_add, add_mul, one_mul, mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    add_zero]
  ext r s
  simp only [diagonal_apply, Matrix.one_apply, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> first | (exfalso; grind) | (field_simp; ring)

private theorem sl_transvection_induction [Nontrivial ι] (P : SpecialLinearGroup ι F → Prop)
    (htrans : ∀ (i j : ι) (hij : i ≠ j) (a : F), P (SpecialLinearGroup.transvection hij a))
    (hmul : ∀ A B, P A → P B → P (A * B)) (A : SpecialLinearGroup ι F) : P A := by
  refine diagonal_transvection_induction' P A ?_ htrans hmul
  intro i j hij a ha
  rw [sl_diag2n_factor hij a ha]
  exact hmul _ _ (hmul _ _ (hmul _ _ (htrans i j hij _) (htrans j i hij.symm _))
    (htrans i j hij _)) (htrans j i hij.symm _)

private noncomputable def sl_iwasawa [Nontrivial ι] :
    MulAction.IwasawaStructure (SpecialLinearGroup ι F) (ℙ F (ι → F)) where
  T p := lineStab p.submodule
  is_comm p := by
    rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
    exact lineStab_isMulCommutative_of_span p.rep
  is_conj g p := by
    rw [PSL.smul_submodule, lineStab_smul]
  is_generator := by
    refine le_antisymm le_top (fun A _ ↦ sl_transvection_induction _ ?_ (fun _ _ ↦ mul_mem) A)
    intro i j hij a
    let e : ι → F := Pi.single i 1
    have he : e ≠ 0 := Pi.single_ne_zero_iff.mpr (one_ne_zero (α := F))
    let p := Projectivization.mk F e he
    apply le_iSup (fun p : ℙ F (ι → F) ↦ lineStab p.submodule) p
    simpa only [p, e, Projectivization.submodule_mk] using SL2Gen.transvection_mem_lineStab hij a

/-- For distinct `i`, `j`, `k`, the commutator of the `(i,k)` and `(k,j)`
transvections is the `(i,j)` transvection. -/
private theorem sl_transvection_commutator {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (a : F) : ⁅SpecialLinearGroup.transvection hik a,
      SpecialLinearGroup.transvection hkj (1 : F)⁆ = SpecialLinearGroup.transvection hij a := by
  let x := SpecialLinearGroup.transvection hik a
  let y := SpecialLinearGroup.transvection hkj (1 : F)
  let z := SpecialLinearGroup.transvection hij a
  have hxy : x * y = z * (y * x) := by
    dsimp only [x, y, z]
    apply coeMonoidHom_injective
    simp only [map_mul]
    simp only [coeMonoidHom_apply, SpecialLinearGroup.transvection_coe, mul_add, add_mul,
      one_mul, mul_one, Matrix.single_mul_single_same,
      Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
      Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm, add_zero]
    abel
  change ⁅x, y⁆ = z
  rw [commutatorElement_def, hxy]
  simp [mul_assoc]

private theorem sl_commutator_eq_top (n : ℕ) (hn : 3 ≤ n) :
    commutator (SpecialLinearGroup (Fin n) (ZMod 5)) = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simpa using (show 1 < n by omega))
  refine le_antisymm le_top (fun A _ ↦ sl_transvection_induction _ ?_ (fun _ _ ↦ mul_mem) A)
  intro i j hij a
  have hcard : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    simpa [hij] using (show 2 < n by omega)
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hik : i ≠ k := fun h ↦ hk (by simp [h])
  have hkj : k ≠ j := fun h ↦ hk (by simp [h])
  rw [← sl_transvection_commutator hij hik hkj a]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem sl_nontrivial (n : ℕ) (hn : 3 ≤ n) :
    Nontrivial (SpecialLinearGroup (Fin n) (ZMod 5)) := by
  have : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simpa using (show 1 < n by omega))
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  refine ⟨⟨SpecialLinearGroup.transvection hij 1, 1, fun h ↦ ?_⟩⟩
  have ht : SpecialLinearGroup.transvection hij (1 : ZMod 5) ∈
      Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 5)) := h ▸ (Subgroup.center _).one_mem
  exact (show (1 : ZMod 5) ≠ 0 by decide) ((transvection_mem_center_iff hij 1).mp ht)

private theorem sl_center_eq_bot (n : ℕ) (hn : 0 < n) (ho : Odd n) :
    Subgroup.center (SpecialLinearGroup (Fin n) (ZMod 5)) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine le_antisymm (fun A hA ↦ ?_) bot_le
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    intro h
    simp [h, zero_pow (ne_of_gt hn)] at hr
  have hcop : n.Coprime 4 := (Nat.coprime_two_right.mpr ho).pow_right 2
  have hd : orderOf r ∣ 1 := hcop.gcd_eq_one ▸
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hr) (ZMod.orderOf_dvd_card_sub_one hr0)
  have hr1 : r = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  apply Subtype.ext
  simpa [hr1, Matrix.scalar_apply] using hscalar.symm

private theorem sl_simple (n : ℕ) (hn : 3 ≤ n) (ho : Odd n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Nontrivial (Fin n) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by simpa using (show 1 < n by omega))
  have := sl_nontrivial n hn
  refine MulAction.IwasawaStructure.isSimpleGroup (sl_commutator_eq_top n hn) sl_iwasawa ?_
  apply faithfulSMul_iff.mpr
  intro g hg
  have hgker : g ∈ (MulAction.toPermHom (SpecialLinearGroup (Fin n) (ZMod 5))
      (ℙ (ZMod 5) (Fin n → ZMod 5))).ker := by
    rw [MonoidHom.mem_ker]
    exact Equiv.ext hg
  rwa [Projectivization.SL_mulAction_ker, sl_center_eq_bot n (by omega) ho,
    Subgroup.mem_bot] at hgker

end

open Matrix

private abbrev F := ZMod 5
private abbrev SL (ι : Type) [Fintype ι] [DecidableEq ι] := Matrix.SpecialLinearGroup ι F

private def NoEigen {ι : Type} [Fintype ι] [DecidableEq ι] (μ : ZMod 5)
    (A : Matrix.SpecialLinearGroup ι (ZMod 5)) :=
  ∀ v : ι → ZMod 5, A • v = μ • v → v = 0

private def Good {ι : Type} [Fintype ι] [DecidableEq ι] :
    Set (Matrix.SpecialLinearGroup ι (ZMod 5)) :=
  {A | (∃ f : (Fin 2 → ZMod 5) →ₗ[ZMod 5] (ι → ZMod 5),
    Function.Injective f ∧ ∀ v, A • f v = f v) ∧ NoEigen (-1) A}

private theorem good_conj {ι : Type} [Fintype ι] [DecidableEq ι]
    (g A : SL ι) (hA : A ∈ Good) : g * A * g⁻¹ ∈ Good := by
  obtain ⟨⟨f, hf, hfix⟩, hne⟩ := hA
  refine ⟨⟨g.toLin'.toLinearMap ∘ₗ f, g.toLin'.injective.comp hf, ?_⟩, ?_⟩
  · intro v
    change (g * A * g⁻¹) • (g • f v) = g • f v
    simp [mul_smul, hfix]
  · intro v hv
    apply g⁻¹.toLin'.injective
    change g⁻¹ • v = g⁻¹ • (0 : ι → F)
    rw [smul_zero]
    apply hne
    have h := congrArg (fun w : ι → F => g⁻¹ • w) hv
    simpa [mul_smul, smul_comm g⁻¹ (-1 : F)] using h

private theorem good_inv {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : SL ι) (hA : A ∈ Good) : A⁻¹ ∈ Good := by
  obtain ⟨⟨f, hf, hfix⟩, hne⟩ := hA
  refine ⟨⟨f, hf, fun v => ?_⟩, ?_⟩
  · simpa using (congrArg (fun w : ι → F => A⁻¹ • w) (hfix v)).symm
  · intro v hv
    change A⁻¹ • v = (-1 : F) • v at hv
    have h : v = -(A • v) := by
      simpa using congrArg (fun w : ι → F => A • w) hv
    apply hne
    simpa using congrArg Neg.neg h.symm

private def reflection (n : ℕ) (hn : Even n) : SL (Fin (n + 1)) :=
  ⟨diagonal (fun i => if i = 0 then 1 else -1), by
    rw [det_diagonal, Fin.prod_univ_succ]
    simp [hn.neg_one_pow]⟩

private theorem reflection_smul_of_apply_zero {n : ℕ} (hn : Even n)
    (v : Fin (n + 1) → F) (hv : v 0 = 0) : reflection n hn • v = -v := by
  ext i
  change (diagonal (fun j : Fin (n + 1) => if j = 0 then (1 : F) else -1) *ᵥ v) i = -v i
  rw [mulVec_diagonal]
  by_cases hi : i = 0
  · simp [hi, hv]
  · simp [hi]

private theorem good_square_ne_univ (n : ℕ) (hn : Even n) :
    (Good : Set (SL (Fin (n + 1)))) * Good ≠ Set.univ := by
  classical
  intro hall
  have hmem : reflection n hn ∈ (Good : Set (SL (Fin (n + 1)))) * Good := by
    rw [hall]
    trivial
  obtain ⟨A, hA, C, hC, hAC⟩ := Set.mem_mul.mp hmem
  obtain ⟨⟨f, hf, hfix⟩, _⟩ := hA
  have hne := (good_inv C hC).2
  let eval : (Fin 2 → F) → F := fun v => (C⁻¹ • f v) 0
  have heval : Function.Injective eval := by
    intro u v huv
    have hz : (C⁻¹ • f (u - v)) 0 = 0 := by
      change (C⁻¹ • f u) 0 = (C⁻¹ • f v) 0 at huv
      rw [map_sub, smul_sub, Pi.sub_apply, huv, sub_self]
    have hh : f (u - v) = -(C⁻¹ • f (u - v)) := calc
      f (u - v) = (A * C) • (C⁻¹ • f (u - v)) := by
        rw [mul_smul, smul_inv_smul, hfix]
      _ = -(C⁻¹ • f (u - v)) := hAC ▸ reflection_smul_of_apply_zero hn _ hz
    have hzero : f (u - v) = 0 := hne _ (by simpa using congrArg Neg.neg hh.symm)
    exact sub_eq_zero.mp (hf (by rw [hzero, map_zero]))
  have hcard := Fintype.card_le_of_injective eval heval
  norm_num [F, ZMod.card] at hcard

private theorem card_sl_ge_dim (n : ℕ) : n ≤ Nat.card (SL (Fin (n + 1))) := by
  classical
  let t (j : Fin n) : SL (Fin (n + 1)) := SpecialLinearGroup.transvection j.succ_ne_zero 1
  have ht : Function.Injective t := by
    intro i j hij
    by_contra hne
    have h : ¬ j = i → (1 : F) = 0 := by
      simpa [t, SpecialLinearGroup.transvection_coe, Matrix.single, i.succ_ne_zero] using
        congrArg (fun A : SL (Fin (n + 1)) => A.1 i.succ 0) hij
    exact (by decide : (1 : F) ≠ 0) (h (Ne.symm hne))
  simpa using Nat.card_le_card_of_injective t ht

private theorem sl_not_comm (n : ℕ) : ∃ a b : SL (Fin (n + 2)), a * b ≠ b * a := by
  let i : Fin (n + 2) := 0
  let j : Fin (n + 2) := Fin.succ (0 : Fin (n + 1))
  have hij : i ≠ j := (Fin.succ_ne_zero _).symm
  let a : SL (Fin (n + 2)) := SpecialLinearGroup.transvection hij 1
  let b : SL (Fin (n + 2)) := SpecialLinearGroup.transvection hij.symm 1
  refine ⟨a, b, fun h => ?_⟩
  have hh := congrArg (fun g : SL (Fin (n + 2)) => (g • (Pi.single i 1 : Fin (n + 2) → F)) i) h
  simp only [mul_smul] at hh
  have hai : a • (Pi.single i 1 : Fin (n + 2) → F) = Pi.single i 1 :=
    SpecialLinearGroup.transvection_smul_single_fst hij _
  have hbi : b • (Pi.single i 1 : Fin (n + 2) → F) = Pi.single i 1 + Pi.single j 1 := by
    simpa [b] using SpecialLinearGroup.transvection_smul_single_snd hij.symm (1 : F)
  have haj : a • (Pi.single j 1 : Fin (n + 2) → F) = Pi.single j 1 + Pi.single i 1 := by
    simpa [a] using SpecialLinearGroup.transvection_smul_single_snd hij (1 : F)
  rw [hbi, smul_add, hai, haj, hbi] at hh
  norm_num [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij] at hh
  exact (by decide : (2 : F) ≠ 1) hh

private theorem exceeds_log_cutoff {G : Type} [Group G] [Finite G] (S : Set G)
    (hsize : 2 ^ 960 < Nat.card G) (hdensity : Nat.card G ≤ 960 * S.ncard) :
    (Nat.card G : ℝ) / Real.logb 2 (Nat.card G) < S.ncard := by
  have hpos : 0 < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hlog : (960 : ℝ) < Real.logb 2 (Nat.card G) := by
    apply (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 2) hpos).2
    change (2 : ℝ) ^ ((960 : ℕ) : ℝ) < (Nat.card G : ℝ)
    rw [Real.rpow_natCast]
    exact_mod_cast hsize
  have hden : (Nat.card G : ℝ) ≤ 960 * S.ncard := by exact_mod_cast hdensity
  calc
    _ < (Nat.card G : ℝ) / 960 := div_lt_div_of_pos_left hpos (by norm_num) hlog
    _ ≤ _ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 960)).2 (by simpa [mul_comm] using hden)


/-- Replace a pivot column of the identity by a given vector, then restore determinant one
by scaling a different column. -/
private theorem density_exists_smul_eq {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Nontrivial ι] [Field F] {u v : ι → F} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup ι F, g • u = v := by
  have fromSingle (w : ι → F) (i : ι) (hi : w i ≠ 0) :
      ∃ g : Matrix.SpecialLinearGroup ι F, g • (Pi.single i 1 : ι → F) = w := by
    obtain ⟨j, hij⟩ := exists_ne i
    let M := Matrix.updateCol (1 : Matrix ι ι F) i w
    have hM : M.det = w i := by
      simpa [M, Matrix.one_apply, eq_comm] using
        Matrix.det_updateCol_sum (1 : Matrix ι ι F) i w
    let N := M.updateCol j ((w i)⁻¹ • fun k => M k j)
    have hN : N.det = 1 := by
      simp [N, Matrix.det_updateCol_smul, hM, hi]
    refine ⟨Matrix.SpecialLinearGroup.mk N hN, ?_⟩
    change N.mulVec (Pi.single i 1 : ι → F) = w
    funext k
    simp [N, M, hij.symm]
  have fromOnes (w : ι → F) (hw : w ≠ 0) :
      ∃ g : Matrix.SpecialLinearGroup ι F, g • (fun _ => (1 : F)) = w := by
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra! h
      exact hw (funext h)
    obtain ⟨g, hg⟩ := fromSingle w i hi
    obtain ⟨h, hh⟩ := fromSingle (fun _ => 1) i one_ne_zero
    refine ⟨g * h⁻¹, ?_⟩
    rw [mul_smul, ← hh, inv_smul_smul, hg]
  obtain ⟨g, hg⟩ := fromOnes u hu
  obtain ⟨h, hh⟩ := fromOnes v hv
  refine ⟨h * g⁻¹, ?_⟩
  rw [mul_smul, ← hg, inv_smul_smul, hh]

private abbrev DensityIncidence (ι : Type) [Fintype ι] [DecidableEq ι] (a : ZMod 5) :=
  Σ v : {v : ι → ZMod 5 // v ≠ 0},
    {A : Matrix.SpecialLinearGroup ι (ZMod 5) // A • v.val = a • v.val}

/-- Translate each incidence fiber to a fiber of evaluation at a fixed nonzero vector. -/
private theorem density_card_incidence {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (a : ZMod 5) (ha : a ≠ 0) :
    Nat.card (DensityIncidence ι a) = Nat.card (Matrix.SpecialLinearGroup ι (ZMod 5)) := by
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let G := Matrix.SpecialLinearGroup ι (ZMod 5)
  let u : ι → ZMod 5 := fun _ => 1
  have hu : u ≠ 0 := by
    intro h
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact one_ne_zero (congrFun h i : (1 : ZMod 5) = 0)
  let f (A : G) : {v : ι → ZMod 5 // v ≠ 0} :=
    ⟨A • u, fun h => hu ((smul_eq_zero_iff_eq A).mp h)⟩
  refine Nat.card_congr ((Equiv.sigmaCongrRight ?_).trans (Equiv.sigmaFiberEquiv f))
  intro v
  have hg₀ := density_exists_smul_eq hu v.property
  have hh₀ := density_exists_smul_eq (smul_ne_zero ha v.property) v.property
  let g := hg₀.choose
  let h := hh₀.choose
  have hg : g • u = v.val := hg₀.choose_spec
  have hh : h • (a • v.val) = v.val := hh₀.choose_spec
  let e : G ≃ G :=
    { toFun := fun A => h * (A * g)
      invFun := fun A => h⁻¹ * (A * g⁻¹)
      left_inv := fun A => by simp [mul_assoc]
      right_inv := fun A => by simp [mul_assoc] }
  refine Equiv.subtypeEquiv e fun A => ?_
  change A • v.val = a • v.val ↔ f (e A) = v
  rw [Subtype.ext_iff]
  change A • v.val = a • v.val ↔ (h * (A * g)) • u = v.val
  calc
    A • v.val = a • v.val ↔ h • (A • v.val) = h • (a • v.val) :=
      (MulAction.injective h).eq_iff.symm
    _ ↔ (h * (A * g)) • u = v.val := by rw [hh, mul_smul, mul_smul, hg]

/-- Each matrix with a nonzero eigenvector contributes all four nonzero scalar multiples. -/
private theorem density_bad_bound {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (a : ZMod 5) (ha : a ≠ 0) :
    4 * ({A : Matrix.SpecialLinearGroup ι (ZMod 5) | ¬ NoEigen a A} : Set _).ncard ≤
      Nat.card (Matrix.SpecialLinearGroup ι (ZMod 5)) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let Bad : Set (Matrix.SpecialLinearGroup ι (ZMod 5)) := {A | ¬ NoEigen a A}
  let Scales : Set (ZMod 5) := ({0} : Set (ZMod 5))ᶜ
  have hbad (A : Bad) : ∃ v : ι → ZMod 5, v ≠ 0 ∧ A.val • v = a • v := by
    by_contra! h
    exact A.property fun v heq => by
      by_contra hv
      exact h v hv heq
  choose v hv heq using hbad
  let f : Bad × Scales → DensityIncidence ι a := fun ⟨A, t⟩ =>
    ⟨⟨t.val • v A, smul_ne_zero (show t.val ≠ 0 from t.property) (hv A)⟩,
      ⟨A.val, by
        change A.val • (t.val • v A) = a • (t.val • v A)
        rw [smul_comm A.val t.val, heq A, smul_comm t.val a]⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨A, s⟩ ⟨B, t⟩ h
    have hAB : A = B := Subtype.ext (congrArg (fun z : DensityIncidence ι a => z.2.val) h)
    subst B
    have hst : s.val • v A = t.val • v A :=
      congrArg (fun z : DensityIncidence ι a => z.1.val) h
    have ht : s = t := Subtype.ext (smul_left_injective (ZMod 5) (hv A) hst)
    rw [ht]
  have hsc : Nat.card Scales = 4 := by
    rw [Nat.card_coe_set_eq]
    change (({0} : Set (ZMod 5))ᶜ).ncard = 4
    rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_zmod]
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, hsc, Nat.card_coe_set_eq, density_card_incidence a ha, mul_comm] at h
  exact h

/-- At least half the matrices have neither a nonzero fixed vector nor a nonzero negated vector. -/
private theorem half_noEigen (m : ℕ) (hm : 2 ≤ m) :
    Nat.card (Matrix.SpecialLinearGroup (Fin m) (ZMod 5)) ≤
      2 * ({A : Matrix.SpecialLinearGroup (Fin m) (ZMod 5) |
        NoEigen 1 A ∧ NoEigen (-1) A} : Set _).ncard := by
  classical
  let _ : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let G := Matrix.SpecialLinearGroup (Fin m) (ZMod 5)
  let Good : Set G := {A | NoEigen 1 A ∧ NoEigen (-1) A}
  change Nat.card G ≤ 2 * Good.ncard
  let B₁ : Set G := {A | ¬ NoEigen 1 A}
  let B₂ : Set G := {A | ¬ NoEigen (-1) A}
  have h₁ : 4 * B₁.ncard ≤ Nat.card G := density_bad_bound (ι := Fin m) 1 one_ne_zero
  have h₂ : 4 * B₂.ncard ≤ Nat.card G :=
    density_bad_bound (ι := Fin m) (-1) (neg_ne_zero.mpr one_ne_zero)
  have hUnion := Set.ncard_union_le B₁ B₂
  have hCompl : (B₁ ∪ B₂)ᶜ = Good := by
    ext A
    simp [B₁, B₂, Good]
  have hTotal := Set.ncard_compl_add_ncard (B₁ ∪ B₂)
  rw [hCompl] at hTotal
  omega

noncomputable section

open Matrix

local notation "K₅" => ZMod 5
private abbrev SL₅ (ι : Type) [DecidableEq ι] [Fintype ι] := Matrix.SpecialLinearGroup ι K₅
private abbrev GL₅ (ι : Type) [DecidableEq ι] [Fintype ι] := Matrix.GeneralLinearGroup ι K₅
private abbrev BlockIndex (m : ℕ) := Fin 2 ⊕ Fin m

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {m : ℕ}

private def blockSL (D : SL₅ (Fin m)) : SL₅ (BlockIndex m) :=
  SpecialLinearGroup.mk (fromBlocks (1 : Matrix (Fin 2) (Fin 2) K₅) 0 0 D.val)
    (by rw [det_fromBlocks_zero₂₁]; simp)

private def blockGL (D : SL₅ (Fin m)) : GL₅ (BlockIndex m) := (blockSL D).toGL

private theorem blockGL_injective : Function.Injective (blockGL (m := m)) := by
  intro D E h
  exact Subtype.ext (congrArg (fun g : GL₅ (BlockIndex m) => g.val.toBlocks₂₂) h)

private def blockConjGL (g : GL₅ (BlockIndex m)) (D : SL₅ (Fin m)) : GL₅ (BlockIndex m) :=
  g * blockGL D * g⁻¹

private def blockConj (g : GL₅ (BlockIndex m)) (D : SL₅ (Fin m)) : SL₅ (BlockIndex m) :=
  SpecialLinearGroup.mk (blockConjGL g D).val (by
    change ((GeneralLinearGroup.det (blockConjGL g D) : K₅ˣ) : K₅) = 1
    have hdet : GeneralLinearGroup.det (blockGL D) = 1 :=
      SpecialLinearGroup.coeToGL_det (blockSL D)
    simp [blockConjGL, hdet])

private def blockLeft : (Fin 2 → K₅) →ₗ[K₅] (BlockIndex m → K₅) where
  toFun v := Sum.elim v 0
  map_add' v w := by
    funext i
    cases i <;> simp
  map_smul' c v := by
    funext i
    cases i <;> simp

private theorem blockLeft_injective : Function.Injective (blockLeft (m := m)) := by
  intro v w h
  funext i
  exact congrFun h (Sum.inl i)

private theorem blockGL_mulVec (D : SL₅ (Fin m)) (v : BlockIndex m → K₅) :
    (blockGL D).val *ᵥ v = Sum.elim (v ∘ Sum.inl) (D.val *ᵥ (v ∘ Sum.inr)) := by
  change fromBlocks (1 : Matrix (Fin 2) (Fin 2) K₅) 0 0 D.val *ᵥ v = _
  simp [fromBlocks_mulVec]

private theorem blockGL_left (D : SL₅ (Fin m)) (v : Fin 2 → K₅) :
    (blockGL D).val *ᵥ blockLeft v = blockLeft v := by
  rw [blockGL_mulVec]
  have hright : (blockLeft v : BlockIndex m → K₅) ∘ Sum.inr = 0 := rfl
  rw [hright, mulVec_zero]
  rfl

private theorem blockGL_noNeg (D : SL₅ (Fin m)) (hD : NoEigen (-1) D)
    (v : BlockIndex m → K₅) (hv : (blockGL D).val *ᵥ v = (-1 : K₅) • v) : v = 0 := by
  rw [blockGL_mulVec] at hv
  have hr : v ∘ Sum.inr = 0 := hD _ (by
    rw [Matrix.SpecialLinearGroup.smul_def]
    funext i
    exact congrFun hv (Sum.inr i))
  funext i
  cases i with
  | inr j => exact congrFun hr j
  | inl j =>
    have hj : v (Sum.inl j) = -v (Sum.inl j) := by
      simpa [Pi.smul_apply] using congrFun hv (Sum.inl j)
    have hzero : (2 : K₅) * v (Sum.inl j) = 0 := by
      rw [two_mul, eq_neg_iff_add_eq_zero.mp hj]
    exact (mul_eq_zero.mp hzero).resolve_left (by decide)

private theorem blockConj_mulVec (g : GL₅ (BlockIndex m)) (D : SL₅ (Fin m))
    (v : BlockIndex m → K₅) :
    blockConj g D • (g.val *ᵥ v) = g.val *ᵥ ((blockGL D).val *ᵥ v) := by
  change (blockConjGL g D).val *ᵥ (g.val *ᵥ v) = g.val *ᵥ ((blockGL D).val *ᵥ v)
  simp only [mulVec_mulVec]
  change (blockConjGL g D * g).val *ᵥ v = (g * blockGL D).val *ᵥ v
  simp [blockConjGL, mul_assoc]

private theorem blockConj_good (g : GL₅ (BlockIndex m)) (D : SL₅ (Fin m))
    (hD : NoEigen (-1) D) : blockConj g D ∈ Good := by
  have hg : Function.Injective g.val.mulVec := mulVec_injective_iff_isUnit.mpr g.isUnit
  refine ⟨⟨g.val.mulVecLin.comp blockLeft, hg.comp blockLeft_injective, ?_⟩, ?_⟩
  · intro v
    change blockConj g D • (g.val *ᵥ blockLeft v) = g.val *ᵥ blockLeft v
    rw [blockConj_mulVec, blockGL_left]
  · intro v hv
    let w := (g⁻¹ : GL₅ (BlockIndex m)).val *ᵥ v
    have hw : g.val *ᵥ w = v := by
      dsimp only [w]
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    rw [← hw, blockConj_mulVec, ← mulVec_smul] at hv
    rw [← hw, blockGL_noNeg D hD w (hg hv), mulVec_zero]

private theorem block_minus_one_isUnit (D : SL₅ (Fin m)) (hD : NoEigen 1 D) :
    IsUnit (D.val - 1) := by
  apply mulVec_injective_iff_isUnit.mp
  intro v w h
  apply sub_eq_zero.mp
  apply hD
  rw [Matrix.SpecialLinearGroup.smul_def, one_smul]
  have hz : (D.val - 1) *ᵥ (v - w) = 0 := by
    rw [mulVec_sub, h, sub_self]
  rwa [sub_mulVec, one_mulVec, sub_eq_zero] at hz

/-- An intertwiner has zero off-diagonal blocks when the lower blocks have no fixed vectors. -/
private theorem block_intertwiner_diagonal (D E : SL₅ (Fin m))
    (hD : NoEigen 1 D) (hE : NoEigen 1 E) (g : GL₅ (BlockIndex m))
    (h : blockGL D * g = g * blockGL E) : g.val.IsTwoBlockDiagonal := by
  have hmat := congrArg (fun z : GL₅ (BlockIndex m) => z.val) h
  change fromBlocks (1 : Matrix (Fin 2) (Fin 2) K₅) 0 0 D.val * g.val =
    g.val * fromBlocks (1 : Matrix (Fin 2) (Fin 2) K₅) 0 0 E.val at hmat
  let A := g.val.toBlocks₁₁
  let B := g.val.toBlocks₁₂
  let C := g.val.toBlocks₂₁
  let F := g.val.toBlocks₂₂
  have hg : fromBlocks A B C F = g.val := fromBlocks_toBlocks _
  rw [← hg, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hmat
  have hB : B = B * E.val := by simpa using hmat.2.1
  have hC : D.val * C = C := by simpa using hmat.2.2.1
  change B = 0 ∧ C = 0
  constructor
  · obtain ⟨u, hu⟩ := block_minus_one_isUnit E hE
    have hz : B * (E.val - 1) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, ← hB, sub_self]
    calc
      B = B * (u.val * (u⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, hu, hz, Matrix.zero_mul]
  · obtain ⟨u, hu⟩ := block_minus_one_isUnit D hD
    have hz : (D.val - 1) * C = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hC, sub_self]
    calc
      C = ((u⁻¹).val * u.val) * C := by rw [Units.inv_mul, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, hu, hz, Matrix.mul_zero]

private theorem block_diagonal_reassemble (g : GL₅ (BlockIndex m))
    (h : g.val.IsTwoBlockDiagonal) : fromBlocks g.val.toBlocks₁₁ 0 0 g.val.toBlocks₂₂ = g.val := by
  simpa only [h.1, h.2] using fromBlocks_toBlocks g.val

private def block_diagonal_units (g : GL₅ (BlockIndex m)) (h : g.val.IsTwoBlockDiagonal) :
    GL₅ (Fin 2) × GL₅ (Fin m) := by
  have hdet : g.val.toBlocks₁₁.det * g.val.toBlocks₂₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ _ 0 _, block_diagonal_reassemble g h]
    exact g.det_ne_zero
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ (mul_ne_zero_iff.mp hdet).1,
    GeneralLinearGroup.mkOfDetNeZero _ (mul_ne_zero_iff.mp hdet).2⟩

private theorem block_diagonal_units_inj (g k : GL₅ (BlockIndex m))
    (hg : g.val.IsTwoBlockDiagonal) (hk : k.val.IsTwoBlockDiagonal)
    (he : block_diagonal_units g hg = block_diagonal_units k hk) : g = k := by
  have h₁ := congrArg (fun p : GL₅ (Fin 2) × GL₅ (Fin m) => p.1.val) he
  have h₂ := congrArg (fun p : GL₅ (Fin 2) × GL₅ (Fin m) => p.2.val) he
  change g.val.toBlocks₁₁ = k.val.toBlocks₁₁ at h₁
  change g.val.toBlocks₂₂ = k.val.toBlocks₂₂ at h₂
  apply Units.ext
  rw [← block_diagonal_reassemble g hg, ← block_diagonal_reassemble k hk, h₁, h₂]

private def blockAdmissible (m : ℕ) : Set (SL₅ (Fin m)) :=
  {D | NoEigen 1 D ∧ NoEigen (-1) D}

private def blockConjToGood (p : GL₅ (BlockIndex m) × blockAdmissible m) :
    (Good : Set (SL₅ (BlockIndex m))) :=
  ⟨blockConj p.1 p.2.val, blockConj_good p.1 p.2.val p.2.property.2⟩

private theorem blockConjToGood_same (x y : GL₅ (BlockIndex m) × blockAdmissible m)
    (h : blockConjToGood x = blockConjToGood y) :
    blockConjGL x.1 x.2.val = blockConjGL y.1 y.2.val :=
  Units.ext (congrArg (fun z : (Good : Set (SL₅ (BlockIndex m))) => z.val.val) h)

private theorem blockConjToGood_relative (x y : GL₅ (BlockIndex m) × blockAdmissible m)
    (h : blockConjToGood x = blockConjToGood y) :
    (x.1⁻¹ * y.1 : GL₅ (BlockIndex m)).val.IsTwoBlockDiagonal := by
  apply block_intertwiner_diagonal x.2.val y.2.val x.2.property.1 y.2.property.1
  calc
    _ = x.1⁻¹ * blockConjGL x.1 x.2.val * y.1 := by simp [blockConjGL, mul_assoc]
    _ = x.1⁻¹ * blockConjGL y.1 y.2.val * y.1 := by rw [blockConjToGood_same x y h]
    _ = _ := by simp [blockConjGL, mul_assoc]

/-- Use one representative to inject a nonempty fiber into the two invertible blocks. -/
private theorem blockConjToGood_fiber_card (A : (Good : Set (SL₅ (BlockIndex m)))) :
    Nat.card {p // blockConjToGood p = A} ≤ Nat.card (GL₅ (Fin 2) × GL₅ (Fin m)) := by
  classical
  by_cases h : Nonempty {p // blockConjToGood p = A}
  · let q := Classical.choice h
    let b (p : {p // blockConjToGood p = A}) := block_diagonal_units
      (q.val.1⁻¹ * p.val.1) (blockConjToGood_relative q.val p.val (q.prop.trans p.prop.symm))
    apply Nat.card_le_card_of_injective b
    intro x y hxy
    have h₁ : x.val.1 = y.val.1 :=
      mul_left_cancel (block_diagonal_units_inj _ _ _ _ hxy)
    have he := blockConjToGood_same x.val y.val (x.prop.trans y.prop.symm)
    have h₂ : x.val.2.val = y.val.2.val := by
      apply blockGL_injective
      rw [blockConjGL, blockConjGL, h₁] at he
      exact mul_left_cancel (mul_right_cancel he)
    exact Subtype.ext (Prod.ext h₁ (Subtype.ext h₂))
  · rw [Nat.card_eq_zero.mpr (Or.inl (not_nonempty_iff.mp h))]
    exact Nat.zero_le _

private theorem blockConj_domain_card_le (m : ℕ) :
    Nat.card (GL₅ (BlockIndex m) × blockAdmissible m) ≤
      Nat.card (Good : Set (SL₅ (BlockIndex m))) * Nat.card (GL₅ (Fin 2) × GL₅ (Fin m)) := by
  classical
  let := Fintype.ofFinite (Good : Set (SL₅ (BlockIndex m)))
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (blockConjToGood (m := m))), Nat.card_sigma]
  calc
    _ ≤ ∑ _ : (Good : Set (SL₅ (BlockIndex m))), Nat.card (GL₅ (Fin 2) × GL₅ (Fin m)) :=
      Finset.sum_le_sum (fun A _ => blockConjToGood_fiber_card A)
    _ = _ := by simp [Nat.card_eq_fintype_card]

private theorem block_card_units : Nat.card K₅ˣ = 4 := by
  rw [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card]

private theorem block_card_GL₂ : Nat.card (GL₅ (Fin 2)) = 480 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  decide

private theorem block_card_GL_fin_le (m : ℕ) :
    Nat.card (GL₅ (Fin m)) ≤ Nat.card (SL₅ (Fin m)) * 4 := by
  cases m with
  | zero =>
    rw [Matrix.card_GL_field, Finset.univ_eq_empty, Finset.prod_empty]
    have hp : 0 < Nat.card (SL₅ (Fin 0)) := Nat.card_pos
    omega
  | succ m => rw [← Matrix.card_SL_mul_card_units, block_card_units]

/-- If at least half of the lower blocks have neither eigenvalue, at least 1/960 of the
larger special linear group is good. The sum coordinates isolate the two fixed dimensions. -/
private theorem good_density_sum (m : ℕ)
    (hhalf : Nat.card (SL₅ (Fin m)) ≤
      2 * {D : SL₅ (Fin m) | NoEigen 1 D ∧ NoEigen (-1) D}.ncard) :
    Nat.card (SL₅ (Fin 2 ⊕ Fin m)) ≤ 960 * (Good : Set (SL₅ (Fin 2 ⊕ Fin m))).ncard := by
  change Nat.card (SL₅ (Fin m)) ≤ 2 * Nat.card (blockAdmissible m) at hhalf
  change Nat.card (SL₅ (BlockIndex m)) ≤ 960 * Nat.card (Good : Set (SL₅ (BlockIndex m)))
  have hbig : Nat.card (SL₅ (BlockIndex m)) * 4 = Nat.card (GL₅ (BlockIndex m)) := by
    rw [← block_card_units, Matrix.card_SL_mul_card_units]
  have h := blockConj_domain_card_le m
  rw [Nat.card_prod, Nat.card_prod, ← hbig, block_card_GL₂] at h
  have hcount : Nat.card (SL₅ (BlockIndex m)) * Nat.card (blockAdmissible m) ≤
      480 * Nat.card (Good : Set (SL₅ (BlockIndex m))) * Nat.card (SL₅ (Fin m)) := by
    apply Nat.le_of_mul_le_mul_right (c := 4) _ (by decide)
    calc
      _ = (Nat.card (SL₅ (BlockIndex m)) * 4) * Nat.card (blockAdmissible m) := by ac_rfl
      _ ≤ Nat.card (Good : Set (SL₅ (BlockIndex m))) * (480 * Nat.card (GL₅ (Fin m))) := h
      _ ≤ Nat.card (Good : Set (SL₅ (BlockIndex m))) *
          (480 * (Nat.card (SL₅ (Fin m)) * 4)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (block_card_GL_fin_le m))
      _ = _ := by ac_rfl
  apply Nat.le_of_mul_le_mul_right (c := Nat.card (SL₅ (Fin m))) _ Nat.card_pos
  calc
    _ ≤ Nat.card (SL₅ (BlockIndex m)) * (2 * Nat.card (blockAdmissible m)) :=
      Nat.mul_le_mul_left _ hhalf
    _ = 2 * (Nat.card (SL₅ (BlockIndex m)) * Nat.card (blockAdmissible m)) := by ac_rfl
    _ ≤ 2 * (480 * Nat.card (Good : Set (SL₅ (BlockIndex m))) * Nat.card (SL₅ (Fin m))) :=
      Nat.mul_le_mul_left _ hcount
    _ = _ := by simp only [← Nat.mul_assoc]

end

private theorem reindex_smul {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (A : SL ι) (v : ι → F) :
    let L := LinearEquiv.piCongrLeft' F (fun _ : ι => F) e
    SpecialLinearGroup.reindex F e A • L v = L (A • v) := by
  funext k
  change (↑(SpecialLinearGroup.reindex F e A) *ᵥ
    (fun j => v (e.symm j))) k = (A.1 *ᵥ v) (e.symm k)
  rw [mulVec_apply, mulVec_apply]
  exact e.symm.sum_comp (fun i : ι => A.val (e.symm k) i * v i)

private theorem reindex_good {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (A : SL ι) (hA : A ∈ Good) :
    SpecialLinearGroup.reindex F e A ∈ Good := by
  obtain ⟨⟨f, hf, hfix⟩, hne⟩ := hA
  let L := LinearEquiv.piCongrLeft' F (fun _ : ι => F) e
  refine ⟨⟨L.toLinearMap ∘ₗ f, L.injective.comp hf, ?_⟩, ?_⟩
  · intro v
    change SpecialLinearGroup.reindex F e A • L (f v) = L (f v)
    rw [reindex_smul, hfix]
  · intro v hv
    obtain ⟨w, rfl⟩ := L.surjective v
    have he : A • w = (-1 : F) • w := L.injective (by
      change L (A • w) = L ((-1 : F) • w)
      rw [← reindex_smul e A w, hv, map_smul])
    rw [hne w he, map_zero]

private theorem good_density_reindex {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (h : Nat.card (SL ι) ≤ 960 * (Good : Set (SL ι)).ncard) :
    Nat.card (SL κ) ≤ 960 * (Good : Set (SL κ)).ncard := by
  let r := SpecialLinearGroup.reindex F e
  rw [← Nat.card_congr r.toEquiv]
  refine h.trans (Nat.mul_le_mul_left _ ?_)
  rw [← Set.ncard_image_of_injective _ r.injective]
  apply Set.ncard_le_ncard (ht := Set.toFinite _)
  rintro _ ⟨A, hA, rfl⟩
  exact reindex_good e A hA

/--
**Pyber's conjecture for finite simple groups is false.** There is no natural number $N$ such that
every nonabelian finite simple group $G$ that has a subset $S$ with $g s g^{-1} \in S$ and
$s^{-1} \in S$ for all $g \in G$ and $s \in S$, with $|S| > |G| / \log_2 |G|$ and with $S^2 \ne G$,
where $S^2 = \{st : s, t \in S\}$, has order $|G| \le N$.

Sheinfeld (Theorem 1.6) gives, for every odd $n \ge 5$, an inverse-closed normal subset $S$ of the
simple group $G = \mathrm{PSL}_n(5) = \mathrm{SL}_n(5)$ with $|S| \ge |G| / 960$ and $S^2 \ne G$, so
infinitely many nonabelian finite simple groups have such a subset; the paper states that this
disproves Pyber's conjecture, and the 21st issue of the Kourovka Notebook records 20.74(a) as "No,
there are infinitely many such groups".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
20.74 (L. Pyber); resolution: O. Sheinfeld, On Shalev's quantitative version of Thompson's
conjecture, preprint, arXiv:2609.22004 (2026) (part (a)); S. V. Skresanov, Bull. London Math. Soc.
57 (2025), no. 11, 3429-3440 (part (b)), (a) Sheinfeld, Theorem 1.6: for every odd n ≥ 5 there is an
inverse-closed normal subset S ⊆ SL_n(5) = PSL_n(5) with |S| ≥ |SL_n(5)|/960 and diag(1, -I_{n-1}) ∉
S², which the paper states disproves Pyber's conjecture; (b) Skresanov, Corollary 3
(arXiv:2406.12506): in a finite simple group of Lie type of bounded rank every inverse-closed normal
subset A with |A| > |G|/log₂|G| has A² = G once |G| is large in terms of the rank, and part (b) for
PSL(2, p) follows; Kourovka Notebook (21st issue), Problem 20.74: a) No, there are infinitely many
such groups; b) The conjecture is proved for the groups PSL(2, p), https://arxiv.org/abs/2609.22004.
-/
public theorem finitelyManySimpleGroupsWithLargeNormalSubset_refuted :
    ¬ finitelyManySimpleGroupsWithLargeNormalSubset := by
  rintro ⟨N, hN⟩
  let k := max N (2 ^ 960)
  let m := 2 * k + 3
  have hm : 3 ≤ m := by dsimp [m]; omega
  have hk : k < m + 1 := by dsimp [m]; omega
  have heven : Even (m + 1) := ⟨k + 2, by dsimp [m]; omega⟩
  have hodd : Odd (m + 2) := ⟨k + 2, by dsimp [m]; omega⟩
  let G := SL (Fin (m + 2))
  have hcard : m + 1 ≤ Nat.card G := card_sl_ge_dim (m + 1)
  have hg : k < Nat.card G := hk.trans_le hcard
  let e : Fin 2 ⊕ Fin m ≃ Fin (m + 2) := finSumFinEquiv.trans (finCongr (Nat.add_comm 2 m))
  have hdensity : Nat.card G ≤ 960 * (Good : Set G).ncard :=
    good_density_reindex e (good_density_sum m (half_noEigen m (by omega)))
  have hlarge : HasLargeInverseClosedNormalSubsetWithSmallSquare G :=
    ⟨Good, good_conj, good_inv,
      exceeds_log_cutoff _ ((le_max_right N (2 ^ 960)).trans_lt hg) hdensity,
      good_square_ne_univ (m + 1) heven⟩
  exact ((le_max_left N (2 ^ 960)).trans_lt hg).not_ge
    (hN G (sl_simple (m + 2) (by omega) hodd) (sl_not_comm m) hlarge)

end MathlibExt.GroupTheory.LargeNormalSubsetSquareKourovka20Problem74Wanted
