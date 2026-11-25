/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_SymmetricPowerPowerSeriesFTSym.lean`
and
`Definitions/Def_SymmetricPowerBlockwiseFTSym.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated definition code. This adaptation restates
the blockwise fixed-point equivalence in Mathlib style, keeps the
supporting single-block and blockwise arguments in an auxiliary
namespace, and adds documentation.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-!
# Blockwise symmetric formal power series

Fix a commutative ring `k`, a finite family of blocks indexed by `Fin m`,
and block sizes `rs : Fin m → ℕ`. A formal power series in the
`∑ j, rs j` variables is blockwise symmetric when it is invariant under
independent permutations of the variables inside each block. The
equivalence `MvPowerSeries.mvPowerSeriesBlockFixedEquiv` identifies the
algebra of such fixed series with the full power series ring: the inverse
map substitutes, for the variable indexed by the `i`-th element of block
`j`, the `(i + 1)`-st elementary symmetric function of that block.
Empty blocks contribute no variables and are allowed.
-/

@[expose] public section

universe u

noncomputable section



namespace MvPowerSeries.BlockwiseAux

section Action

variable (k : Type u) [CommRing k] (r : ℕ)

@[reducible]
def permMulSemiringActionMvPowerSeries :
    MulSemiringAction (Equiv.Perm (Fin r)) (MvPowerSeries (Fin r) k) where
  smul σ p := MvPowerSeries.renameEquiv k σ p
  one_smul p := by
    show MvPowerSeries.renameEquiv k (1 : Equiv.Perm (Fin r)) p = p
    rw [Equiv.Perm.one_def, MvPowerSeries.renameEquiv_refl]; rfl
  mul_smul σ τ p := by
    show MvPowerSeries.renameEquiv k (σ * τ) p =
      MvPowerSeries.renameEquiv k σ (MvPowerSeries.renameEquiv k τ p)
    have : σ * τ = Equiv.trans τ σ := rfl
    rw [this, ← MvPowerSeries.renameEquiv_trans]
    rfl
  smul_zero σ := map_zero _
  smul_add σ p q := map_add _ p q
  smul_one σ := map_one _
  smul_mul σ p q := map_mul _ p q

@[reducible]
def permSMulCommClassMvPowerSeries :
    letI := permMulSemiringActionMvPowerSeries k r
    SMulCommClass (Equiv.Perm (Fin r)) k (MvPowerSeries (Fin r) k) := by
  letI := permMulSemiringActionMvPowerSeries k r
  refine ⟨fun σ c p => ?_⟩
  show MvPowerSeries.renameEquiv k σ (c • p) = c • MvPowerSeries.renameEquiv k σ p
  exact map_smul _ c p

end Action

namespace PowerSeriesFTSym

variable {k : Type u} [CommRing k] {r : ℕ}

variable (k r) in
def es (i : Fin r) : MvPolynomial (Fin r) k := MvPolynomial.esymm (Fin r) k (i + 1)

variable (k r) in
def ea (i : Fin r) : MvPowerSeries (Fin r) k := (es k r i : MvPowerSeries (Fin r) k)

theorem esymm_isHomogeneous (n : ℕ) : (MvPolynomial.esymm (Fin r) k n).IsHomogeneous n := by
  show MvPolynomial.IsHomogeneous
    (∑ t ∈ Finset.powersetCard n Finset.univ,
      ∏ i ∈ t, (MvPolynomial.X i : MvPolynomial (Fin r) k)) n
  apply MvPolynomial.IsHomogeneous.sum
  intro t ht
  have h := MvPolynomial.IsHomogeneous.prod t
    (fun i : Fin r => (MvPolynomial.X i : MvPolynomial (Fin r) k))
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X k i)
  rwa [Finset.sum_const, smul_eq_mul, mul_one, (Finset.mem_powersetCard.mp ht).2] at h

theorem constantCoeff_ea (i : Fin r) : MvPowerSeries.constantCoeff (ea k r i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ea, MvPolynomial.coeff_coe]
  exact (esymm_isHomogeneous (i + 1)).coeff_eq_zero (by simp)

variable (k r) in
theorem hasSubst_ea : MvPowerSeries.HasSubst (ea k r) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero constantCoeff_ea

def wt (d : Fin r →₀ ℕ) : ℕ := d.sum fun i n => ((i : ℕ) + 1) * n

theorem le_wt (d : Fin r →₀ ℕ) (i : Fin r) : d i ≤ wt d := by
  by_cases hi : i ∈ d.support
  · calc d i ≤ ((i : ℕ) + 1) * d i := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      _ ≤ wt d := Finset.single_le_sum
          (f := fun j : Fin r => ((j : ℕ) + 1) * d j) (fun _ _ => Nat.zero_le _) hi
  · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _

def eP (d : Fin r →₀ ℕ) : MvPolynomial (Fin r) k := d.prod fun i n => es k r i ^ n

theorem eP_isHomogeneous (d : Fin r →₀ ℕ) : (eP (k := k) d).IsHomogeneous (wt d) :=
  MvPolynomial.IsHomogeneous.prod d.support (fun i => es k r i ^ d i) (fun i => ((i : ℕ) + 1) * d i)
    fun i _ => (esymm_isHomogeneous (i + 1)).pow (d i)

theorem prod_ea_eq_coe_eP (d : Fin r →₀ ℕ) :
    (d.prod fun s n => ea k r s ^ n)
      = ((eP d : MvPolynomial (Fin r) k) : MvPowerSeries (Fin r) k) := by
  simp only [Finsupp.prod, eP, ea]
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply]

def bnd (N : ℕ) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N

def wtSet (r : ℕ) (N : ℕ) : Finset (Fin r →₀ ℕ) :=
  (Finset.Iic (bnd N)).filter fun d => wt d = N

theorem mem_wtSet {N : ℕ} {d : Fin r →₀ ℕ} : d ∈ wtSet r N ↔ wt d = N := by
  rw [wtSet, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
  intro h i
  rw [bnd, Finsupp.coe_equivFunOnFinite_symm]
  exact h ▸ le_wt d i

def degSet (r : ℕ) (N : ℕ) : Finset (Fin r →₀ ℕ) :=
  (Finset.Iic (bnd N)).filter fun e => e.degree = N

theorem mem_degSet {N : ℕ} {e : Fin r →₀ ℕ} : e ∈ degSet r N ↔ e.degree = N := by
  rw [degSet, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
  intro h i
  rw [bnd, Finsupp.coe_equivFunOnFinite_symm]
  exact h ▸ Finsupp.le_degree i e

theorem coeff_aeval_es (q : MvPolynomial (Fin r) k) (e : Fin r →₀ ℕ) :
    (MvPolynomial.aeval (es k r) q).coeff e
      = ∑ d ∈ wtSet r e.degree, q.coeff d * (eP (k := k) d).coeff e := by
  conv_lhs => rw [q.as_sum, map_sum, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]
  change ∑ d ∈ q.support, q.coeff d * (eP (k := k) d).coeff e = _
  rw [← Finset.sum_filter_add_sum_filter_not q.support (fun d => wt d = e.degree)]
  have h0 : ∑ d ∈ q.support.filter (fun d => ¬ wt d = e.degree),
      q.coeff d * (eP (k := k) d).coeff e = 0 :=
    Finset.sum_eq_zero fun d hd => by
      rw [(eP_isHomogeneous d).coeff_eq_zero (Ne.symm (Finset.mem_filter.mp hd).2), mul_zero]
  rw [h0, add_zero]
  have hset : q.support.filter (fun d => wt d = e.degree)
      = (wtSet r e.degree).filter (· ∈ q.support) := by
    ext d
    simp only [Finset.mem_filter, mem_wtSet]
    exact and_comm
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, zero_mul]

theorem coeff_subst_ea (f : MvPowerSeries (Fin r) k) (e : Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst (ea k r) f)
      = ∑ d ∈ wtSet r e.degree, MvPowerSeries.coeff d f * (eP (k := k) d).coeff e := by
  rw [MvPowerSeries.coeff_subst (hasSubst_ea k r)]
  rw [finsum_eq_sum_of_support_subset _ (s := wtSet r e.degree) ?_]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [prod_ea_eq_coe_eP, MvPolynomial.coeff_coe, smul_eq_mul]
  · intro d hd
    rw [Function.mem_support, prod_ea_eq_coe_eP, MvPolynomial.coeff_coe] at hd
    rw [Finset.mem_coe, mem_wtSet]
    by_contra hne
    exact hd (by rw [(eP_isHomogeneous d).coeff_eq_zero (Ne.symm hne), smul_zero])

theorem aeval_truncFinset_isHomogeneous (f : MvPowerSeries (Fin r) k) (N : ℕ) :
    (MvPolynomial.aeval (es k r) (MvPowerSeries.truncFinset k (wtSet r N) f)).IsHomogeneous N := by
  rw [MvPowerSeries.truncFinset_apply, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, ← mem_wtSet.mp hd]
  exact (eP_isHomogeneous d).C_mul _

theorem coeff_subst_ea_eq_coeff_aeval (f : MvPowerSeries (Fin r) k) (e : Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst (ea k r) f)
      = (MvPolynomial.aeval (es k r)
          (MvPowerSeries.truncFinset k (wtSet r e.degree) f)).coeff e := by
  rw [coeff_subst_ea, coeff_aeval_es]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPowerSeries.coeff_truncFinset_of_mem _ hd]

theorem aeval_es_injective : Function.Injective (MvPolynomial.aeval (R := k) (es k r)) := by
  intro p q h
  apply (MvPolynomial.esymmAlgHom_fin_bijective (R := k) r).1
  apply Subtype.ext
  rw [MvPolynomial.esymmAlgHom_apply, MvPolynomial.esymmAlgHom_apply]
  exact h

theorem subst_ea_injective :
    Function.Injective (MvPowerSeries.subst (R := k) (ea k r)) := by
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_ea k r)]
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  rw [MvPowerSeries.coe_substAlgHom] at hf
  ext d

  have hP : MvPolynomial.aeval (es k r) (MvPowerSeries.truncFinset k (wtSet r (wt d)) f) = 0 := by
    ext e
    by_cases he : e.degree = wt d
    · rw [← he, ← coeff_subst_ea_eq_coeff_aeval, hf, map_zero]
      simp
    · rw [(aeval_truncFinset_isHomogeneous f (wt d)).coeff_eq_zero he]
      simp
  have h0 : MvPowerSeries.truncFinset k (wtSet r (wt d)) f = 0 :=
    aeval_es_injective (by rw [hP, map_zero])
  have := congrArg (fun p => p.coeff d) h0
  rwa [MvPowerSeries.coeff_truncFinset_of_mem _ (mem_wtSet.mpr rfl),
    MvPolynomial.coeff_zero] at this

theorem rename_subst_ea (σ : Equiv.Perm (Fin r)) (f : MvPowerSeries (Fin r) k) :
    MvPowerSeries.rename σ (MvPowerSeries.subst (ea k r) f) = MvPowerSeries.subst (ea k r) f := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_ea k r) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext i
  rw [← MvPowerSeries.rename_eq_subst, ea, MvPowerSeries.rename_coe, es, MvPolynomial.rename_esymm]

theorem coeff_mapDomain_of_fixed {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) (τ : Equiv.Perm (Fin r))
    (x : Fin r →₀ ℕ) : MvPowerSeries.coeff (Finsupp.mapDomain τ x) g = MvPowerSeries.coeff x g := by
  conv_lhs => rw [← hg τ]
  have h : Finsupp.embDomain τ.toEmbedding x = Finsupp.mapDomain τ x :=
    Finsupp.embDomain_eq_mapDomain _ _
  rw [← h]
  exact MvPowerSeries.coeff_embDomain_rename τ.toEmbedding g x

theorem truncFinset_degSet_isSymmetric {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) (N : ℕ) :
    (MvPowerSeries.truncFinset k (degSet r N) g).IsSymmetric := by
  intro σ
  ext e
  have he : e = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm e) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [he, MvPolynomial.coeff_rename_mapDomain σ σ.injective, ← he]
  by_cases hN : e ∈ degSet r N
  · have hN' : Finsupp.mapDomain σ.symm e ∈ degSet r N := by
      rw [mem_degSet] at hN ⊢; rw [Finsupp.degree_mapDomain]; exact hN
    rw [MvPowerSeries.coeff_truncFinset_of_mem _ hN, MvPowerSeries.coeff_truncFinset_of_mem _ hN',
      coeff_mapDomain_of_fixed hg]
  · have hN' : Finsupp.mapDomain σ.symm e ∉ degSet r N := by
      rw [mem_degSet] at hN ⊢; rw [Finsupp.degree_mapDomain]; exact hN
    rw [MvPowerSeries.coeff_truncFinset_eq_zero _ hN, MvPowerSeries.coeff_truncFinset_eq_zero _ hN']

theorem exists_aeval_eq_truncFinset {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) (N : ℕ) :
    ∃ q : MvPolynomial (Fin r) k,
      MvPolynomial.aeval (es k r) q = MvPowerSeries.truncFinset k (degSet r N) g := by
  obtain ⟨q, hq⟩ := (MvPolynomial.esymmAlgHom_fin_bijective (R := k) r).2
    ⟨_, truncFinset_degSet_isSymmetric hg N⟩
  refine ⟨q, ?_⟩
  have := congrArg Subtype.val hq
  rwa [MvPolynomial.esymmAlgHom_apply] at this

theorem exists_subst_ea_eq {g : MvPowerSeries (Fin r) k}
    (hg : ∀ σ : Equiv.Perm (Fin r), MvPowerSeries.rename σ g = g) :
    ∃ f : MvPowerSeries (Fin r) k, MvPowerSeries.subst (ea k r) f = g := by
  choose q hq using exists_aeval_eq_truncFinset hg
  refine ⟨(fun d => (q (wt d)).coeff d : MvPowerSeries (Fin r) k), ?_⟩
  ext e
  calc MvPowerSeries.coeff e (MvPowerSeries.subst (ea k r)
          (fun d => (q (wt d)).coeff d : MvPowerSeries (Fin r) k))
        = ∑ d ∈ wtSet r e.degree, MvPowerSeries.coeff d
            (fun d => (q (wt d)).coeff d : MvPowerSeries (Fin r) k)
            * (eP (k := k) d).coeff e := coeff_subst_ea _ _
    _ = ∑ d ∈ wtSet r e.degree,
            (q e.degree).coeff d * (eP (k := k) d).coeff e :=
          Finset.sum_congr rfl fun d hd => by
            rw [show MvPowerSeries.coeff d (fun d => (q (wt d)).coeff d)
              = (q (wt d)).coeff d from rfl, mem_wtSet.mp hd]
    _ = (MvPolynomial.aeval (es k r) (q e.degree)).coeff e := (coeff_aeval_es _ _).symm
    _ = MvPowerSeries.coeff e g := by
          rw [hq, MvPowerSeries.coeff_truncFinset_of_mem _ (mem_degSet.mpr rfl)]

end PowerSeriesFTSym

end MvPowerSeries.BlockwiseAux


namespace MvPowerSeries

open FixedPoints


variable (k : Type u) [CommRing k]

def blockPermEmbed (m : ℕ) (rs : Fin m → ℕ) :
    (∀ j, Equiv.Perm (Fin (rs j))) →* Equiv.Perm (Fin (∑ j, rs j)) := by
  induction m with
  | zero => exact 1
  | succ m ih =>
    refine MonoidHom.comp ?_ (MonoidHom.prod
      (ih (rs ∘ Fin.castSucc) |>.comp (MonoidHom.pi fun j =>
        Pi.evalMonoidHom _ (Fin.castSucc j)))
      (Pi.evalMonoidHom _ (Fin.last m)))
    refine MonoidHom.comp ?_ (Equiv.Perm.sumCongrHom _ _)
    exact (Equiv.permCongrHom
      (finSumFinEquiv.trans (finCongr (Fin.sum_univ_castSucc rs).symm))).toMonoidHom

@[reducible]
public def blockPermMulSemiringAction (m : ℕ) (rs : Fin m → ℕ) :
    MulSemiringAction (∀ j, Equiv.Perm (Fin (rs j))) (MvPowerSeries (Fin (∑ j, rs j)) k) :=
  letI := BlockwiseAux.permMulSemiringActionMvPowerSeries k (∑ j, rs j)
  MulSemiringAction.compHom _ (blockPermEmbed m rs)

@[reducible]
public def blockPermSMulCommClass (m : ℕ) (rs : Fin m → ℕ) :
    letI := blockPermMulSemiringAction k m rs
    SMulCommClass (∀ j, Equiv.Perm (Fin (rs j))) k (MvPowerSeries (Fin (∑ j, rs j)) k) := by
  letI := BlockwiseAux.permMulSemiringActionMvPowerSeries k (∑ j, rs j)
  letI := BlockwiseAux.permSMulCommClassMvPowerSeries k (∑ j, rs j)
  letI := blockPermMulSemiringAction k m rs
  exact ⟨fun σ c p => smul_comm (blockPermEmbed m rs σ) c p⟩

variable {k}

section BlockIn

variable (m : ℕ) (rs : Fin (m + 1) → ℕ)

abbrev stepIdx :
    Fin (∑ j, (rs ∘ Fin.castSucc) j) ⊕ Fin (rs (Fin.last m)) ≃ Fin (∑ j, rs j) :=
  finSumFinEquiv.trans (finCongr (Fin.sum_univ_castSucc rs).symm)

theorem blockPermEmbed_succ (σ : ∀ j, Equiv.Perm (Fin (rs j))) :
    blockPermEmbed (m + 1) rs σ = (stepIdx m rs).permCongr
      (Equiv.sumCongr (blockPermEmbed m (rs ∘ Fin.castSucc) (fun j => σ (Fin.castSucc j)))
        (σ (Fin.last m))) := rfl

end BlockIn

variable {m : ℕ} {rs : Fin m → ℕ}

def blockIn : ∀ {m : ℕ} {rs : Fin m → ℕ} (j : Fin m), Fin (rs j) → Fin (∑ j, rs j)
  | 0, _, j, _ => j.elim0
  | _ + 1, rs, j, i =>
    j.lastCases (fun i => stepIdx _ rs (Sum.inr i))
      (fun j' i => stepIdx _ rs (Sum.inl (blockIn j' i))) i

theorem blockIn_last {rs : Fin (m + 1) → ℕ} (i : Fin (rs (Fin.last m))) :
    blockIn (rs := rs) (Fin.last m) i = stepIdx m rs (Sum.inr i) := by
  simp only [blockIn, Fin.lastCases_last]

theorem blockIn_castSucc {rs : Fin (m + 1) → ℕ} (j : Fin m)
    (i : Fin ((rs ∘ Fin.castSucc) j)) :
    blockIn (rs := rs) (Fin.castSucc j) i = stepIdx m rs (Sum.inl (blockIn j i)) := by
  simp only [blockIn, Fin.lastCases_castSucc]

@[simp] theorem blockPermEmbed_apply (σ : ∀ j, Equiv.Perm (Fin (rs j))) (j : Fin m)
    (i : Fin (rs j)) :
    (blockPermEmbed m rs σ) (blockIn j i) = blockIn j (σ j i) := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    revert i
    refine Fin.lastCases ?_ ?_ j
    · intro i
      rw [blockIn_last, blockIn_last, blockPermEmbed_succ,
        Equiv.permCongr_apply, Equiv.symm_apply_apply]
      rfl
    · intro j' i
      rw [blockIn_castSucc, blockIn_castSucc, blockPermEmbed_succ,
        Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply, Sum.map_inl,
        ih (rs := rs ∘ Fin.castSucc) (fun j => σ (Fin.castSucc j)) j' i]

theorem blockIn_injective (j : Fin m) : Function.Injective (blockIn (rs := rs) j) := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    intro i i' h
    revert h i i'
    refine Fin.lastCases ?_ ?_ j
    · intro i i' h
      rw [blockIn_last, blockIn_last] at h
      exact Sum.inr_injective ((stepIdx m rs).injective h)
    · intro j' i i' h
      rw [blockIn_castSucc, blockIn_castSucc] at h
      exact ih (rs := rs ∘ Fin.castSucc) j' (Sum.inl_injective ((stepIdx m rs).injective h))

theorem blockIn_eq_finSigmaFinEquiv (j : Fin m) (i : Fin (rs j)) :
    blockIn (rs := rs) j i = finSigmaFinEquiv ⟨j, i⟩ := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    have hval : ∀ {n : ℕ} {rs' : Fin n → ℕ} (j' : Fin n) (i' : Fin (rs' j')),
        ((finSigmaFinEquiv ⟨j', i'⟩ : Fin (∑ j, rs' j)) : ℕ)
          = ∑ a : Fin j'.1, rs' (Fin.castLE j'.2.le a) + (i' : ℕ) :=
      fun j' i' => finSigmaFinEquiv_apply ⟨j', i'⟩
    apply Fin.ext
    revert i
    refine Fin.lastCases ?_ ?_ j
    · intro i
      rw [blockIn_last, hval]
      show ((finCongr (Fin.sum_univ_castSucc rs).symm : Fin _ ≃ Fin _)
          (finSumFinEquiv (Sum.inr i)) : ℕ) = _
      simp only [finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_right, Fin.val_natAdd]
      exact congrArg (· + (i : ℕ))
        (Finset.sum_congr rfl fun a _ => congrArg rs (Fin.ext rfl))
    · intro j' i
      rw [blockIn_castSucc, hval]
      show ((finCongr (Fin.sum_univ_castSucc rs).symm : Fin _ ≃ Fin _)
          (finSumFinEquiv (Sum.inl (blockIn (rs := rs ∘ Fin.castSucc) j' i))) : ℕ) = _
      simp only [finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_left, Fin.val_castAdd]
      rw [Fin.ext_iff.mp (ih (rs := rs ∘ Fin.castSucc) j' i), hval]
      exact congrArg (· + (i : ℕ))
        (Finset.sum_congr rfl fun a _ => congrArg rs (Fin.ext rfl))

open BlockwiseAux BlockwiseAux.PowerSeriesFTSym

namespace BlockwiseFTSym

abbrev toBlock (l : Fin (∑ j, rs j)) : (j : Fin m) × Fin (rs j) :=
  (finSigmaFinEquiv (n := rs)).symm l

theorem toBlock_blockIn (j : Fin m) (i : Fin (rs j)) :
    toBlock (rs := rs) (blockIn (rs := rs) j i) = ⟨j, i⟩ := by
  rw [toBlock, blockIn_eq_finSigmaFinEquiv, Equiv.symm_apply_apply]

variable (k m rs) in
def bes (l : Fin (∑ j, rs j)) : MvPolynomial (Fin (∑ j, rs j)) k :=
  let ⟨j, i⟩ := toBlock l
  MvPolynomial.rename (blockIn (rs := rs) j) (MvPolynomial.esymm (Fin (rs j)) k (i + 1))

theorem bes_blockIn_gen (j : Fin m) (i : Fin (rs j)) :
    bes k m rs (blockIn (rs := rs) j i)
      = MvPolynomial.rename (blockIn (rs := rs) j) (MvPolynomial.esymm (Fin (rs j)) k (i + 1)) := by
  unfold bes
  rw [toBlock_blockIn]

variable (k m rs) in
def bea (l : Fin (∑ j, rs j)) : MvPowerSeries (Fin (∑ j, rs j)) k :=
  (bes k m rs l : MvPowerSeries (Fin (∑ j, rs j)) k)

theorem bes_isHomogeneous (l : Fin (∑ j, rs j)) :
    (bes k m rs l).IsHomogeneous ((toBlock l).2 + 1) := by
  unfold bes
  rcases hjl : toBlock (rs := rs) l with ⟨j, i⟩
  simp only
  exact (esymm_isHomogeneous (k := k) (r := rs j) (i + 1)).rename_isHomogeneous

theorem constantCoeff_bea (l : Fin (∑ j, rs j)) :
    MvPowerSeries.constantCoeff (bea k m rs l) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, bea, MvPolynomial.coeff_coe]
  exact (bes_isHomogeneous l).coeff_eq_zero (by simp)

variable (k m rs) in
theorem hasSubst_bea : MvPowerSeries.HasSubst (bea k m rs) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero constantCoeff_bea

def bwt (d : Fin (∑ j, rs j) →₀ ℕ) : ℕ :=
  d.sum fun l n => (((toBlock l).2 : ℕ) + 1) * n

theorem le_bwt (d : Fin (∑ j, rs j) →₀ ℕ) (l : Fin (∑ j, rs j)) : d l ≤ bwt d := by
  by_cases hl : l ∈ d.support
  · calc d l ≤ ((((toBlock l).2 : ℕ)) + 1) * d l := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      _ ≤ bwt d := Finset.single_le_sum
          (f := fun l => (((toBlock l).2 : ℕ) + 1) * d l) (fun _ _ => Nat.zero_le _) hl
  · rw [Finsupp.notMem_support_iff.mp hl]; exact Nat.zero_le _

end BlockwiseFTSym

namespace BlockwiseFTSym

variable (k m rs) in
def IsBlockSymmetric (p : MvPolynomial (Fin (∑ j, rs j)) k) : Prop :=
  ∀ σ : ∀ j, Equiv.Perm (Fin (rs j)), MvPolynomial.rename (blockPermEmbed m rs σ) p = p

theorem bes_isBlockSymmetric (l : Fin (∑ j, rs j)) :
    IsBlockSymmetric k m rs (bes k m rs l) := by
  intro σ
  unfold bes
  rcases hjl : toBlock (rs := rs) l with ⟨j, i⟩
  simp only
  have hkey : ((blockPermEmbed m rs σ) : _ → _) ∘ (blockIn (rs := rs) j)
      = (blockIn (rs := rs) j) ∘ (σ j) :=
    funext fun i' => blockPermEmbed_apply σ j i'
  rw [MvPolynomial.rename_rename, hkey, ← MvPolynomial.rename_rename,
    MvPolynomial.rename_esymm]

theorem rename_aeval_bes (σ : ∀ j, Equiv.Perm (Fin (rs j)))
    (q : MvPolynomial (Fin (∑ j, rs j)) k) :
    MvPolynomial.rename (blockPermEmbed m rs σ) (MvPolynomial.aeval (bes k m rs) q)
      = MvPolynomial.aeval (bes k m rs) q := by
  have h : (MvPolynomial.rename (R := k) (blockPermEmbed m rs σ)).comp
      (MvPolynomial.aeval (bes k m rs)) = MvPolynomial.aeval (bes k m rs) :=
    MvPolynomial.algHom_ext fun l => by
      simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_X]
      exact bes_isBlockSymmetric l σ
  exact DFunLike.congr_fun h q

section MapFixedPoints

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
  {σ : Type*}

@[reducible]
def mapMulSemiringAction : MulSemiringAction G (MvPolynomial σ R) where
  smul g p := MvPolynomial.map (MulSemiringAction.toRingHom G R g) p
  one_smul p := by
    show MvPolynomial.map _ p = p
    rw [show MulSemiringAction.toRingHom G R 1 = RingHom.id R from RingHom.ext (one_smul G)]
    exact MvPolynomial.map_id p
  mul_smul g h p := by
    show MvPolynomial.map _ p = MvPolynomial.map _ (MvPolynomial.map _ p)
    rw [MvPolynomial.map_map]
    exact congrArg (fun φ => MvPolynomial.map φ p)
      (RingHom.ext fun r => mul_smul g h r)
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _
  smul_one _ := map_one _
  smul_mul _ _ _ := map_mul _ _ _

theorem map_fixed_iff_coeff (p : MvPolynomial σ R) :
    letI := mapMulSemiringAction (R := R) (G := G) (σ := σ)
    (∀ g : G, g • p = p) ↔ ∀ d, ∀ g : G, g • p.coeff d = p.coeff d := by
  letI := mapMulSemiringAction (R := R) (G := G) (σ := σ)
  constructor
  · intro hp d g
    have := congrArg (fun p => p.coeff d) (hp g)
    rwa [show g • p = MvPolynomial.map (MulSemiringAction.toRingHom G R g) p from rfl,
      MvPolynomial.coeff_map] at this
  · intro hc g
    refine MvPolynomial.ext _ _ fun d => ?_
    rw [show g • p = MvPolynomial.map (MulSemiringAction.toRingHom G R g) p from rfl,
      MvPolynomial.coeff_map]
    exact hc d g

end MapFixedPoints

section Step

variable (k) {m : ℕ} (rs : Fin (m + 1) → ℕ)

def psiX : MvPolynomial (Fin (∑ j, rs j)) k ≃ₐ[k]
    MvPolynomial (Fin (rs (Fin.last m))) (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k) :=
  (MvPolynomial.renameEquiv k ((stepIdx m rs).symm.trans (Equiv.sumComm _ _))).trans
    (MvPolynomial.sumAlgEquiv k _ _)

theorem stepIdx_symm_blockIn_last (i : Fin (rs (Fin.last m))) :
    ((stepIdx m rs).symm.trans (Equiv.sumComm _ _)) (blockIn (rs := rs) (Fin.last m) i)
      = Sum.inl i := by
  rw [blockIn_last, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumComm_apply, Sum.swap_inr]

theorem stepIdx_symm_blockIn_castSucc (j : Fin m) (i : Fin ((rs ∘ Fin.castSucc) j)) :
    ((stepIdx m rs).symm.trans (Equiv.sumComm _ _)) (blockIn (rs := rs) (Fin.castSucc j) i)
      = Sum.inr (blockIn (rs := rs ∘ Fin.castSucc) j i) := by
  rw [blockIn_castSucc, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumComm_apply,
    Sum.swap_inl]

theorem psiX_rename_blockIn_last (p : MvPolynomial (Fin (rs (Fin.last m))) k) :
    psiX k rs (MvPolynomial.rename (blockIn (rs := rs) (Fin.last m)) p)
      = MvPolynomial.map (algebraMap k _) p := by
  have key : (psiX k rs).toAlgHom.comp (MvPolynomial.rename (blockIn (rs := rs) (Fin.last m)))
      = MvPolynomial.mapAlgHom
          (Algebra.ofId k (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k)) := by
    rw [show (psiX k rs).toAlgHom
        = (MvPolynomial.sumAlgEquiv k _ _).toAlgHom.comp
            (MvPolynomial.rename ((stepIdx m rs).symm.trans (Equiv.sumComm _ _))) from rfl,
      AlgHom.comp_assoc, MvPolynomial.rename_comp_rename,
      show ((stepIdx m rs).symm.trans (Equiv.sumComm _ _) : _ → _)
          ∘ blockIn (rs := rs) (Fin.last m) = Sum.inl from
        funext fun i => stepIdx_symm_blockIn_last rs i]
    exact MvPolynomial.sumAlgEquiv_comp_rename_inl k _ _
  exact DFunLike.congr_fun key p

theorem psiX_rename_blockIn_castSucc (j : Fin m)
    (p : MvPolynomial (Fin ((rs ∘ Fin.castSucc) j)) k) :
    psiX k rs (MvPolynomial.rename (blockIn (rs := rs) (Fin.castSucc j)) p)
      = MvPolynomial.C (MvPolynomial.rename (blockIn (rs := rs ∘ Fin.castSucc) j) p) := by
  have key : (psiX k rs).toAlgHom.comp (MvPolynomial.rename (blockIn (rs := rs) (Fin.castSucc j)))
      = (IsScalarTower.toAlgHom k (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k) _).comp
          (MvPolynomial.rename (blockIn (rs := rs ∘ Fin.castSucc) j)) := by
    rw [show (psiX k rs).toAlgHom
        = (MvPolynomial.sumAlgEquiv k _ _).toAlgHom.comp
            (MvPolynomial.rename ((stepIdx m rs).symm.trans (Equiv.sumComm _ _))) from rfl,
      AlgHom.comp_assoc, MvPolynomial.rename_comp_rename,
      show ((stepIdx m rs).symm.trans (Equiv.sumComm _ _) : _ → _)
          ∘ blockIn (rs := rs) (Fin.castSucc j)
          = (Sum.inr : Fin _ → _) ∘ blockIn (rs := rs ∘ Fin.castSucc) j from
        funext fun i => stepIdx_symm_blockIn_castSucc rs j i,
      ← MvPolynomial.sumAlgEquiv_comp_rename_inr k _ _,
      AlgHom.comp_assoc, MvPolynomial.rename_comp_rename]
  exact DFunLike.congr_fun key p

theorem psiX_bes_last (i : Fin (rs (Fin.last m))) :
    psiX k rs (bes k (m + 1) rs (finSigmaFinEquiv ⟨Fin.last m, i⟩))
      = MvPolynomial.map (algebraMap k _)
          (MvPolynomial.esymm (Fin (rs (Fin.last m))) k (i + 1)) := by
  rw [show bes k (m + 1) rs (finSigmaFinEquiv ⟨Fin.last m, i⟩)
      = MvPolynomial.rename (blockIn (rs := rs) (Fin.last m))
          (MvPolynomial.esymm (Fin (rs (Fin.last m))) k (i + 1)) from by
    unfold bes toBlock; rw [Equiv.symm_apply_apply]]
  exact psiX_rename_blockIn_last k rs _

theorem psiX_bes_castSucc (j : Fin m) (i : Fin ((rs ∘ Fin.castSucc) j)) :
    psiX k rs (bes k (m + 1) rs (finSigmaFinEquiv ⟨Fin.castSucc j, i⟩))
      = MvPolynomial.C (bes k m (rs ∘ Fin.castSucc) (finSigmaFinEquiv ⟨j, i⟩)) := by
  rw [show bes k (m + 1) rs (finSigmaFinEquiv ⟨Fin.castSucc j, i⟩)
      = MvPolynomial.rename (blockIn (rs := rs) (Fin.castSucc j))
          (MvPolynomial.esymm (Fin (rs (Fin.castSucc j))) k (i + 1)) from by
    unfold bes toBlock; rw [Equiv.symm_apply_apply],
    psiX_rename_blockIn_castSucc k rs j,
    show bes k m (rs ∘ Fin.castSucc) (finSigmaFinEquiv ⟨j, i⟩)
      = MvPolynomial.rename (blockIn (rs := rs ∘ Fin.castSucc) j)
          (MvPolynomial.esymm (Fin ((rs ∘ Fin.castSucc) j)) k (i + 1)) from by
    unfold bes toBlock; rw [Equiv.symm_apply_apply]]
  rfl

theorem bes_blockIn (j : Fin (m + 1)) (i : Fin (rs j)) :
    bes k (m + 1) rs (blockIn (rs := rs) j i)
      = MvPolynomial.rename (blockIn (rs := rs) j) (MvPolynomial.esymm (Fin (rs j)) k (i + 1)) := by
  unfold bes
  rw [toBlock_blockIn]

theorem psiX_symm_X (i : Fin (rs (Fin.last m))) :
    (psiX k rs).symm (MvPolynomial.X i)
      = MvPolynomial.X (blockIn (rs := rs) (Fin.last m) i) := by
  rw [AlgEquiv.symm_apply_eq, ← MvPolynomial.rename_X (blockIn (rs := rs) (Fin.last m)) i,
    psiX_rename_blockIn_last, MvPolynomial.map_X]

theorem psiX_symm_C (r : MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k) :
    (psiX k rs).symm (MvPolynomial.C r)
      = MvPolynomial.rename (fun l => stepIdx m rs (Sum.inl l)) r := by
  rw [AlgEquiv.symm_apply_eq]
  have key : (psiX k rs).toAlgHom.comp
      (MvPolynomial.rename (fun l => stepIdx m rs (Sum.inl l)))
      = IsScalarTower.toAlgHom k (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k) _ := by
    rw [show (psiX k rs).toAlgHom
        = (MvPolynomial.sumAlgEquiv k _ _).toAlgHom.comp
            (MvPolynomial.rename ((stepIdx m rs).symm.trans (Equiv.sumComm _ _))) from rfl,
      AlgHom.comp_assoc, MvPolynomial.rename_comp_rename,
      show ((stepIdx m rs).symm.trans (Equiv.sumComm _ _) : _ → _)
          ∘ (fun l => stepIdx m rs (Sum.inl l)) = Sum.inr from
        funext fun l => by
          rw [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply,
            Equiv.sumComm_apply, Sum.swap_inl]]
    exact MvPolynomial.sumAlgEquiv_comp_rename_inr k _ _
  exact (DFunLike.congr_fun key r).symm

theorem step_conjugate :
    ((psiX k rs).toAlgHom.comp (MvPolynomial.aeval (bes k (m + 1) rs))).comp
        (psiX k rs).symm.toAlgHom
      = ((MvPolynomial.aeval (R := MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k)
            (es (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k)
              (rs (Fin.last m)))).restrictScalars k).comp
          (MvPolynomial.mapAlgHom (R := k)
            (MvPolynomial.aeval (bes k m (rs ∘ Fin.castSucc)))) := by
  refine AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext ?_ ?_)
  ·
    intro r
    simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgHom.restrictScalars_apply]
    rw [psiX_symm_C, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_C, MvPolynomial.aeval_C]
    change _ = MvPolynomial.C (MvPolynomial.aeval _ r)
    have lhs_is : ∀ r', psiX k rs (MvPolynomial.aeval (bes k (m + 1) rs)
        (MvPolynomial.rename (fun l => stepIdx m rs (Sum.inl l)) r'))
        = ((psiX k rs).toAlgHom.comp ((MvPolynomial.aeval (bes k (m + 1) rs)).comp
            (MvPolynomial.rename (fun l => stepIdx m rs (Sum.inl l))))) r' := fun _ => rfl
    have rhs_is : ∀ r', (MvPolynomial.C (MvPolynomial.aeval (bes k m (rs ∘ Fin.castSucc)) r')
        : MvPolynomial (Fin (rs (Fin.last m))) _)
        = ((IsScalarTower.toAlgHom k (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k) _).comp
            (MvPolynomial.aeval (bes k m (rs ∘ Fin.castSucc)))) r' := fun _ => rfl
    rw [lhs_is, rhs_is]
    refine DFunLike.congr_fun (MvPolynomial.algHom_ext fun l' => ?_) r
    rw [← lhs_is, ← rhs_is, MvPolynomial.rename_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    obtain ⟨⟨j', i'⟩, rfl⟩ :=
      (finSigmaFinEquiv (n := rs ∘ Fin.castSucc)).surjective l'
    rw [← blockIn_eq_finSigmaFinEquiv, ← blockIn_castSucc, bes_blockIn,
      psiX_rename_blockIn_castSucc]
    congr 1
    exact (bes_blockIn_gen (k := k) (rs := rs ∘ Fin.castSucc) j' i').symm
  ·
    intro i
    simp only [AlgHom.coe_toRingHom, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgHom.restrictScalars_apply]
    rw [psiX_symm_X, MvPolynomial.aeval_X, bes_blockIn, psiX_rename_blockIn_last,
      MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X, MvPolynomial.aeval_X]
    show _ = MvPolynomial.esymm _ _ (i + 1)
    exact MvPolynomial.map_esymm _ _ _ _

end Step

section StepEquivariance

variable (k : Type u) [CommRing k] {m : ℕ} (rs : Fin (m + 1) → ℕ)

theorem psiX_rename_blockPermEmbed (σ : ∀ j, Equiv.Perm (Fin (rs j)))
    (p : MvPolynomial (Fin (∑ j, rs j)) k) :
    psiX k rs (MvPolynomial.rename (blockPermEmbed (m + 1) rs σ) p)
      = MvPolynomial.rename (σ (Fin.last m))
          (MvPolynomial.map (MvPolynomial.rename (R := k)
            (blockPermEmbed m (rs ∘ Fin.castSucc) (fun j => σ (Fin.castSucc j)))).toRingHom
            (psiX k rs p)) := by
  refine DFunLike.congr_fun (AlgHom.coe_ringHom_injective (MvPolynomial.ringHom_ext ?_ ?_) :
    (psiX k rs).toAlgHom.comp (MvPolynomial.rename (blockPermEmbed (m + 1) rs σ))
      = ((MvPolynomial.rename (R := MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k)
          (σ (Fin.last m))).restrictScalars k).comp
          ((MvPolynomial.mapAlgHom (R := k)
            (MvPolynomial.rename (blockPermEmbed m (rs ∘ Fin.castSucc)
              (fun j => σ (Fin.castSucc j))))).comp (psiX k rs).toAlgHom)) p
  ·
    intro c
    show psiX k rs (MvPolynomial.rename _ (MvPolynomial.C c))
      = MvPolynomial.rename _ (MvPolynomial.mapAlgHom _ (psiX k rs (MvPolynomial.C c)))
    rw [MvPolynomial.rename_C,
      show (MvPolynomial.C c : MvPolynomial (Fin (∑ j, rs j)) k) = algebraMap k _ c from rfl,
      AlgEquiv.commutes, MvPolynomial.mapAlgHom_apply,
      show (algebraMap k (MvPolynomial (Fin (rs (Fin.last m))) (MvPolynomial (Fin _) k))) c
        = MvPolynomial.C (MvPolynomial.C c) from rfl,
      MvPolynomial.map_C, MvPolynomial.rename_C]
    exact congrArg MvPolynomial.C (MvPolynomial.rename_C _ _).symm
  ·
    intro l
    show psiX k rs (MvPolynomial.rename _ (MvPolynomial.X l))
      = MvPolynomial.rename _ (MvPolynomial.mapAlgHom _ (psiX k rs (MvPolynomial.X l)))
    rw [MvPolynomial.rename_X]
    obtain ⟨⟨j, i⟩, rfl⟩ := (finSigmaFinEquiv (n := rs)).surjective l
    rw [← blockIn_eq_finSigmaFinEquiv, blockPermEmbed_apply]
    revert i
    refine Fin.lastCases ?_ ?_ j
    · intro i
      rw [← MvPolynomial.rename_X (blockIn _) (σ _ i),
        ← MvPolynomial.rename_X (blockIn (rs := rs) (Fin.last m)) i,
        psiX_rename_blockIn_last, psiX_rename_blockIn_last,
        MvPolynomial.mapAlgHom_apply, MvPolynomial.map_map]
      simp only [MvPolynomial.map_X, MvPolynomial.rename_X]
    · intro j' i
      rw [← MvPolynomial.rename_X (blockIn _) (σ _ i),
        ← MvPolynomial.rename_X (blockIn (rs := rs) (Fin.castSucc j')) i,
        psiX_rename_blockIn_castSucc, psiX_rename_blockIn_castSucc,
        MvPolynomial.mapAlgHom_apply, MvPolynomial.map_C, MvPolynomial.rename_C]
      congr 1
      show (MvPolynomial.rename (blockIn (rs := rs ∘ Fin.castSucc) j'))
          (MvPolynomial.X (R := k) (σ (Fin.castSucc j') i))
        = MvPolynomial.rename
            (blockPermEmbed m (rs ∘ Fin.castSucc) (fun j => σ (Fin.castSucc j)))
            (MvPolynomial.rename (blockIn (rs := rs ∘ Fin.castSucc) j') (MvPolynomial.X i))
      rw [MvPolynomial.rename_X, MvPolynomial.rename_X, MvPolynomial.rename_X,
        blockPermEmbed_apply]

theorem isSymmetric_psiX_of_isBlockSymmetric {p : MvPolynomial (Fin (∑ j, rs j)) k}
    (hp : IsBlockSymmetric k (m + 1) rs p) : (psiX k rs p).IsSymmetric := by
  intro τ
  have key := (psiX_rename_blockPermEmbed k rs (Fin.lastCases τ (fun _ => 1)) p).symm
  rw [hp _, Fin.lastCases_last] at key

  have hσ' : (fun j => Fin.lastCases (motive := fun j => Equiv.Perm (Fin (rs j)))
      τ (fun _ => 1) (Fin.castSucc j) : ∀ j, Equiv.Perm (Fin ((rs ∘ Fin.castSucc) j))) = 1 :=
    funext fun j => Fin.lastCases_castSucc ..
  have h1 : blockPermEmbed m (rs ∘ Fin.castSucc)
      (fun j => Fin.lastCases (motive := fun j => Equiv.Perm (Fin (rs j)))
        τ (fun _ => 1) (Fin.castSucc j)) = 1 := hσ' ▸ map_one _
  have hring : (MvPolynomial.rename (R := k)
      (⇑(blockPermEmbed m (rs ∘ Fin.castSucc)
        (fun j => Fin.lastCases (motive := fun j => Equiv.Perm (Fin (rs j)))
          τ (fun _ => 1) (Fin.castSucc j))))).toRingHom
      = RingHom.id (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k) := by
    rw [h1]
    exact RingHom.ext fun x => by
      show MvPolynomial.rename
        (⇑(1 : Equiv.Perm (Fin (∑ j, (rs ∘ Fin.castSucc) j)))) x = x
      rw [Equiv.Perm.coe_one]; exact DFunLike.congr_fun MvPolynomial.rename_id x
  rw [hring, MvPolynomial.map_id] at key
  exact key

theorem coeff_psiX_isBlockSymmetric {p : MvPolynomial (Fin (∑ j, rs j)) k}
    (hp : IsBlockSymmetric k (m + 1) rs p) (d) :
    IsBlockSymmetric k m (rs ∘ Fin.castSucc) ((psiX k rs p).coeff d) := by
  intro σ'
  have key := (psiX_rename_blockPermEmbed k rs (Fin.lastCases 1 σ') p).symm
  rw [hp _, Fin.lastCases_last,
    show (fun j => Fin.lastCases (motive := fun j => Equiv.Perm (Fin (rs j))) 1 σ' (Fin.castSucc j))
      = σ' from funext fun j => Fin.lastCases_castSucc ..] at key
  rw [Equiv.Perm.coe_one, MvPolynomial.rename_id, AlgHom.id_apply] at key
  calc (MvPolynomial.rename (R := k) (blockPermEmbed m (rs ∘ Fin.castSucc) σ'))
        ((psiX k rs p).coeff d)
      = (MvPolynomial.map (MvPolynomial.rename (R := k)
            (blockPermEmbed m (rs ∘ Fin.castSucc) σ')).toRingHom (psiX k rs p)).coeff d :=
        (MvPolynomial.coeff_map _ _ _).symm
    _ = (psiX k rs p).coeff d := by rw [key]

end StepEquivariance

variable (k m rs) in
theorem aeval_bes_injective :
    Function.Injective (MvPolynomial.aeval (R := k) (bes k m rs)) := by
  induction m with
  | zero =>
    have hz : ∑ j : Fin 0, rs j = 0 := by simp
    have hid : MvPolynomial.aeval (R := k) (bes k 0 rs) = AlgHom.id k _ :=
      MvPolynomial.algHom_ext fun i => (Fin.cast hz i).elim0
    rw [hid]
    exact fun _ _ h => h
  | succ m ih =>
    have hconj := step_conjugate k rs
    have heq : ∀ q,
        psiX k rs (MvPolynomial.aeval (bes k (m + 1) rs) q)
          = (((MvPolynomial.aeval (R := MvPolynomial _ k)
              (es (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k)
                (rs (Fin.last m)))).restrictScalars k).comp
            (MvPolynomial.mapAlgHom (R := k)
              (MvPolynomial.aeval (bes k m (rs ∘ Fin.castSucc))))) (psiX k rs q) := fun q => by
      have := DFunLike.congr_fun hconj (psiX k rs q)
      rwa [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
        AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply] at this
    intro q q' h
    have h' : psiX k rs (MvPolynomial.aeval _ q) = psiX k rs (MvPolynomial.aeval _ q') :=
      congrArg _ h
    rw [heq, heq] at h'
    have hinj1 : Function.Injective
        (MvPolynomial.aeval (R := MvPolynomial _ k)
          (es (MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k) (rs (Fin.last m)))) :=
      aeval_es_injective
    have hinj2 : Function.Injective
        (MvPolynomial.mapAlgHom (R := k) (σ := Fin (rs (Fin.last m)))
          (MvPolynomial.aeval (bes k m (rs ∘ Fin.castSucc)))) := by
      intro a b hab
      simp only [MvPolynomial.mapAlgHom_apply] at hab
      exact MvPolynomial.map_injective _
        (fun x y hxy => ih (rs := rs ∘ Fin.castSucc) hxy) hab
    exact (psiX k rs).injective (hinj2 (hinj1 h'))

variable (k m rs) in
theorem exists_aeval_bes_eq {p : MvPolynomial (Fin (∑ j, rs j)) k}
    (hp : IsBlockSymmetric k m rs p) :
    ∃ q, MvPolynomial.aeval (R := k) (bes k m rs) q = p := by
  induction m with
  | zero =>
    refine ⟨p, ?_⟩
    have hz : ∑ j : Fin 0, rs j = 0 := by simp
    rw [show MvPolynomial.aeval (R := k) (bes k 0 rs) = AlgHom.id k _ from
      MvPolynomial.algHom_ext fun i => (Fin.cast hz i).elim0, AlgHom.id_apply]
  | succ m ih =>
    set R' := MvPolynomial (Fin (∑ j, (rs ∘ Fin.castSucc) j)) k
    obtain ⟨q1, hq1⟩ := (MvPolynomial.esymmAlgHom_fin_bijective
      (R := R') (rs (Fin.last m))).2
      ⟨psiX k rs p, isSymmetric_psiX_of_isBlockSymmetric k rs hp⟩
    have hq1' : MvPolynomial.aeval (R := R') (es R' (rs (Fin.last m))) q1 = psiX k rs p := by
      have := congrArg Subtype.val hq1
      rwa [MvPolynomial.esymmAlgHom_apply] at this
    have hcomm : ∀ (φ : R' →ₐ[k] R') (q : MvPolynomial (Fin (rs (Fin.last m))) R'),
        MvPolynomial.map φ.toRingHom (MvPolynomial.aeval (R := R') (es R' (rs (Fin.last m))) q)
          = MvPolynomial.aeval (R := R') (es R' (rs (Fin.last m)))
              (MvPolynomial.map φ.toRingHom q) := fun φ q => by
      refine DFunLike.congr_fun (MvPolynomial.ringHom_ext ?_ ?_ :
        ((MvPolynomial.map φ.toRingHom).comp
          (MvPolynomial.aeval (R := R') (es R' _)).toRingHom
          : MvPolynomial (Fin (rs (Fin.last m))) R' →+* MvPolynomial (Fin (rs (Fin.last m))) R')
          = (MvPolynomial.aeval (R := R') (es R' _)).toRingHom.comp
              (MvPolynomial.map φ.toRingHom)) q
      · intro r
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        simp only [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        rw [MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.aeval_X]
        exact (MvPolynomial.map_esymm _ _ _ _).trans rfl
    have hcoeff_q1 : ∀ d, IsBlockSymmetric k m (rs ∘ Fin.castSucc)
        (q1.coeff d) := by
      intro d σ'
      have hfix : MvPolynomial.map (MvPolynomial.rename (R := k)
          (blockPermEmbed m (rs ∘ Fin.castSucc) σ')).toRingHom q1 = q1 := by
        apply aeval_es_injective (k := R') (r := rs (Fin.last m))
        rw [← hcomm, hq1']
        refine MvPolynomial.ext_iff.mpr fun e => ?_
        rw [MvPolynomial.coeff_map]
        exact coeff_psiX_isBlockSymmetric k rs hp e σ'
      calc (MvPolynomial.rename (R := k) (blockPermEmbed m (rs ∘ Fin.castSucc) σ'))
            (q1.coeff d)
          = (MvPolynomial.map (MvPolynomial.rename (R := k)
              (blockPermEmbed m (rs ∘ Fin.castSucc) σ')).toRingHom q1).coeff d :=
            (MvPolynomial.coeff_map _ _ _).symm
        _ = q1.coeff d := by rw [hfix]
    choose rfd hrfd using fun d => ih (rs := rs ∘ Fin.castSucc) (hcoeff_q1 d)
    refine ⟨(psiX k rs).symm (∑ d ∈ q1.support, MvPolynomial.monomial d (rfd d)), ?_⟩
    apply (psiX k rs).injective
    have hconj := DFunLike.congr_fun (step_conjugate k rs)
      (psiX k rs ((psiX k rs).symm (∑ d ∈ q1.support, MvPolynomial.monomial d (rfd d))))
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      AlgEquiv.toAlgHom_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply] at hconj
    rw [hconj, AlgHom.comp_apply, MvPolynomial.mapAlgHom_apply, map_sum,
      ← hq1', AlgHom.restrictScalars_apply]
    congr 1
    refine Eq.trans (Finset.sum_congr rfl fun d _ => ?_)
      (MvPolynomial.support_sum_monomial_coeff q1)
    rw [MvPolynomial.map_monomial]
    exact congrArg (MvPolynomial.monomial d) (hrfd d)

def beP (d : Fin (∑ j, rs j) →₀ ℕ) : MvPolynomial (Fin (∑ j, rs j)) k :=
  d.prod fun l n => bes k m rs l ^ n

theorem beP_isHomogeneous (d : Fin (∑ j, rs j) →₀ ℕ) :
    (beP (k := k) (rs := rs) d).IsHomogeneous (bwt d) :=
  MvPolynomial.IsHomogeneous.prod d.support (fun l => bes k m rs l ^ d l)
    (fun l => (((toBlock l).2 : ℕ) + 1) * d l)
    fun l _ => (bes_isHomogeneous l).pow (d l)

theorem prod_bea_eq_coe_beP (d : Fin (∑ j, rs j) →₀ ℕ) :
    (d.prod fun l n => bea k m rs l ^ n)
      = ((beP d : MvPolynomial (Fin (∑ j, rs j)) k) : MvPowerSeries _ k) := by
  simp only [Finsupp.prod, beP, bea]
  rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply]

def bwtSet (N : ℕ) : Finset (Fin (∑ j, rs j) →₀ ℕ) :=
  (Finset.Iic (bnd N)).filter fun d => bwt d = N

theorem mem_bwtSet {N : ℕ} {d : Fin (∑ j, rs j) →₀ ℕ} :
    d ∈ bwtSet (rs := rs) N ↔ bwt d = N := by
  rw [bwtSet, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
  intro h l
  rw [bnd, Finsupp.coe_equivFunOnFinite_symm]
  exact h ▸ le_bwt d l

theorem coeff_aeval_bes (q : MvPolynomial (Fin (∑ j, rs j)) k) (e : Fin (∑ j, rs j) →₀ ℕ) :
    (MvPolynomial.aeval (bes k m rs) q).coeff e
      = ∑ d ∈ bwtSet e.degree,
          q.coeff d * (beP (k := k) (rs := rs) d).coeff e := by
  conv_lhs => rw [q.as_sum, map_sum, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul]
  change ∑ d ∈ q.support, q.coeff d * (beP (k := k) d).coeff e = _
  rw [← Finset.sum_filter_add_sum_filter_not q.support (fun d => bwt d = e.degree)]
  have h0 : ∑ d ∈ q.support.filter (fun d => ¬ bwt d = e.degree),
      q.coeff d * (beP (k := k) (rs := rs) d).coeff e = 0 :=
    Finset.sum_eq_zero fun d hd => by
      rw [(beP_isHomogeneous d).coeff_eq_zero (Ne.symm (Finset.mem_filter.mp hd).2), mul_zero]
  rw [h0, add_zero]
  have hset : q.support.filter (fun d => bwt d = e.degree)
      = (bwtSet (rs := rs) e.degree).filter (· ∈ q.support) := by
    ext d
    simp only [Finset.mem_filter, mem_bwtSet]
    exact and_comm
  rw [hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, zero_mul]

theorem coeff_subst_bea (f : MvPowerSeries (Fin (∑ j, rs j)) k) (e : Fin (∑ j, rs j) →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst (bea k m rs) f)
      = ∑ d ∈ bwtSet e.degree,
          MvPowerSeries.coeff d f * (beP (k := k) (rs := rs) d).coeff e := by
  rw [MvPowerSeries.coeff_subst (hasSubst_bea k m rs)]
  rw [finsum_eq_sum_of_support_subset _ (s := bwtSet (rs := rs) e.degree) ?_]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [prod_bea_eq_coe_beP, MvPolynomial.coeff_coe, smul_eq_mul]
  · intro d hd
    rw [Function.mem_support, prod_bea_eq_coe_beP, MvPolynomial.coeff_coe] at hd
    rw [Finset.mem_coe, mem_bwtSet]
    by_contra hne
    exact hd (by rw [(beP_isHomogeneous d).coeff_eq_zero (Ne.symm hne), smul_zero])

theorem aeval_truncFinset_isHomogeneous (f : MvPowerSeries (Fin (∑ j, rs j)) k) (N : ℕ) :
    (MvPolynomial.aeval (bes k m rs)
      (MvPowerSeries.truncFinset k (bwtSet (rs := rs) N) f)).IsHomogeneous N := by
  rw [MvPowerSeries.truncFinset_apply, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, ← mem_bwtSet.mp hd]
  exact (beP_isHomogeneous d).C_mul _

theorem coeff_subst_bea_eq_coeff_aeval (f : MvPowerSeries (Fin (∑ j, rs j)) k)
    (e : Fin (∑ j, rs j) →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.subst (bea k m rs) f)
      = (MvPolynomial.aeval (bes k m rs)
          (MvPowerSeries.truncFinset k (bwtSet (rs := rs) e.degree) f)).coeff e := by
  rw [coeff_subst_bea, coeff_aeval_bes]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPowerSeries.coeff_truncFinset_of_mem _ hd]

theorem subst_bea_injective :
    Function.Injective (MvPowerSeries.subst (R := k) (bea k m rs)) := by
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_bea k m rs)]
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  rw [MvPowerSeries.coe_substAlgHom] at hf
  ext d
  have hP : MvPolynomial.aeval (bes k m rs)
      (MvPowerSeries.truncFinset k (bwtSet (rs := rs) (bwt d)) f) = 0 := by
    ext e
    by_cases he : e.degree = bwt d
    · rw [← he, ← coeff_subst_bea_eq_coeff_aeval, hf, map_zero]
      simp
    · rw [(aeval_truncFinset_isHomogeneous f (bwt d)).coeff_eq_zero he]
      simp
  have h0 : MvPowerSeries.truncFinset k (bwtSet (rs := rs) (bwt d)) f = 0 :=
    aeval_bes_injective k m rs (by rw [hP, map_zero])
  have := congrArg (fun p => p.coeff d) h0
  rwa [MvPowerSeries.coeff_truncFinset_of_mem _ (mem_bwtSet.mpr rfl), MvPolynomial.coeff_zero]
    at this

theorem rename_subst_bea (σ : ∀ j, Equiv.Perm (Fin (rs j)))
    (f : MvPowerSeries (Fin (∑ j, rs j)) k) :
    MvPowerSeries.rename (blockPermEmbed m rs σ) (MvPowerSeries.subst (bea k m rs) f)
      = MvPowerSeries.subst (bea k m rs) f := by
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_bea k m rs) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext l
  rw [← MvPowerSeries.rename_eq_subst, bea, MvPowerSeries.rename_coe]
  exact congrArg _ (bes_isBlockSymmetric l σ)

theorem coeff_mapDomain_of_fixed {g : MvPowerSeries (Fin (∑ j, rs j)) k}
    (hg : ∀ σ : ∀ j, Equiv.Perm (Fin (rs j)),
      MvPowerSeries.rename (blockPermEmbed m rs σ) g = g)
    (τ : ∀ j, Equiv.Perm (Fin (rs j))) (x : Fin (∑ j, rs j) →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.mapDomain (blockPermEmbed m rs τ) x) g
      = MvPowerSeries.coeff x g := by
  conv_lhs => rw [← hg τ]
  have h : Finsupp.embDomain (blockPermEmbed m rs τ).toEmbedding x
      = Finsupp.mapDomain (blockPermEmbed m rs τ) x := Finsupp.embDomain_eq_mapDomain _ _
  rw [← h]
  exact MvPowerSeries.coeff_embDomain_rename (blockPermEmbed m rs τ).toEmbedding g x

theorem truncFinset_degSet_isBlockSymmetric {g : MvPowerSeries (Fin (∑ j, rs j)) k}
    (hg : ∀ σ : ∀ j, Equiv.Perm (Fin (rs j)),
      MvPowerSeries.rename (blockPermEmbed m rs σ) g = g) (N : ℕ) :
    IsBlockSymmetric k m rs (MvPowerSeries.truncFinset k (degSet (∑ j, rs j) N) g) := by
  intro σ
  have hsymm : ((blockPermEmbed m rs σ) : Equiv.Perm _).symm = blockPermEmbed m rs σ⁻¹ :=
    (map_inv (blockPermEmbed m rs) σ).symm
  ext e
  have he : e = Finsupp.mapDomain (blockPermEmbed m rs σ)
      (Finsupp.mapDomain (blockPermEmbed m rs σ).symm e) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [he, MvPolynomial.coeff_rename_mapDomain _ (blockPermEmbed m rs σ).injective, ← he]
  by_cases hN : e ∈ degSet (∑ j, rs j) N
  · have hN' : Finsupp.mapDomain (blockPermEmbed m rs σ).symm e ∈ degSet (∑ j, rs j) N := by
      rw [mem_degSet] at hN ⊢; rw [Finsupp.degree_mapDomain]; exact hN
    rw [MvPowerSeries.coeff_truncFinset_of_mem _ hN,
      MvPowerSeries.coeff_truncFinset_of_mem _ hN', hsymm, coeff_mapDomain_of_fixed hg]
  · have hN' : Finsupp.mapDomain (blockPermEmbed m rs σ).symm e ∉ degSet (∑ j, rs j) N := by
      rw [mem_degSet] at hN ⊢; rw [Finsupp.degree_mapDomain]; exact hN
    rw [MvPowerSeries.coeff_truncFinset_eq_zero _ hN,
      MvPowerSeries.coeff_truncFinset_eq_zero _ hN']

theorem exists_aeval_eq_truncFinset_block {g : MvPowerSeries (Fin (∑ j, rs j)) k}
    (hg : ∀ σ : ∀ j, Equiv.Perm (Fin (rs j)),
      MvPowerSeries.rename (blockPermEmbed m rs σ) g = g) (N : ℕ) :
    ∃ q : MvPolynomial (Fin (∑ j, rs j)) k,
      MvPolynomial.aeval (bes k m rs) q
        = MvPowerSeries.truncFinset k (degSet (∑ j, rs j) N) g :=
  exists_aeval_bes_eq k m rs (truncFinset_degSet_isBlockSymmetric hg N)

theorem exists_subst_bea_eq {g : MvPowerSeries (Fin (∑ j, rs j)) k}
    (hg : ∀ σ : ∀ j, Equiv.Perm (Fin (rs j)),
      MvPowerSeries.rename (blockPermEmbed m rs σ) g = g) :
    ∃ f : MvPowerSeries (Fin (∑ j, rs j)) k, MvPowerSeries.subst (bea k m rs) f = g := by
  choose q hq using exists_aeval_eq_truncFinset_block hg
  refine ⟨(fun d => (q (bwt d)).coeff d : MvPowerSeries (Fin (∑ j, rs j)) k), ?_⟩
  ext e
  calc MvPowerSeries.coeff e (MvPowerSeries.subst (bea k m rs)
          (fun d => (q (bwt d)).coeff d : MvPowerSeries (Fin (∑ j, rs j)) k))
        = ∑ d ∈ bwtSet (rs := rs) e.degree,
            MvPowerSeries.coeff d
              (fun d => (q (bwt d)).coeff d : MvPowerSeries (Fin (∑ j, rs j)) k)
              * (beP (k := k) (rs := rs) d).coeff e := coeff_subst_bea _ _
    _ = ∑ d ∈ bwtSet (rs := rs) e.degree,
            (q e.degree).coeff d * (beP (k := k) d).coeff e :=
          Finset.sum_congr rfl fun d hd => by
            rw [show MvPowerSeries.coeff d (fun d => (q (bwt d)).coeff d)
              = (q (bwt d)).coeff d from rfl, mem_bwtSet.mp hd]
    _ = (MvPolynomial.aeval (bes k m rs) (q e.degree)).coeff e :=
          (coeff_aeval_bes _ _).symm
    _ = MvPowerSeries.coeff e g := by
          rw [hq, MvPowerSeries.coeff_truncFinset_of_mem _ (mem_degSet.mpr rfl)]

end BlockwiseFTSym

open BlockwiseFTSym

variable (k) (m : ℕ) (rs : Fin m → ℕ)

def substBlockEsymmAlgHom :
    letI := blockPermMulSemiringAction k m rs
    letI := blockPermSMulCommClass k m rs
    MvPowerSeries (Fin (∑ j, rs j)) k →ₐ[k]
      FixedPoints.subalgebra k (MvPowerSeries (Fin (∑ j, rs j)) k)
        (∀ j, Equiv.Perm (Fin (rs j))) :=
  letI := blockPermMulSemiringAction k m rs
  letI := blockPermSMulCommClass k m rs
  (MvPowerSeries.substAlgHom (hasSubst_bea k m rs)).codRestrict _ fun f σ => by
    change MvPowerSeries.renameEquiv k (blockPermEmbed m rs σ)
      (MvPowerSeries.substAlgHom (hasSubst_bea k m rs) f) = _
    rw [MvPowerSeries.coe_substAlgHom]
    exact rename_subst_bea σ f

theorem substBlockEsymmAlgHom_apply_coe (f : MvPowerSeries (Fin (∑ j, rs j)) k) :
    letI := blockPermMulSemiringAction k m rs
    letI := blockPermSMulCommClass k m rs
    ((substBlockEsymmAlgHom k m rs f : _) : MvPowerSeries (Fin (∑ j, rs j)) k)
      = MvPowerSeries.subst (bea k m rs) f := by
  change MvPowerSeries.substAlgHom (hasSubst_bea k m rs) f = _
  rw [MvPowerSeries.coe_substAlgHom]

theorem substBlockEsymmAlgHom_bijective :
    Function.Bijective (substBlockEsymmAlgHom k m rs) := by
  letI := blockPermMulSemiringAction k m rs
  letI := blockPermSMulCommClass k m rs
  constructor
  · intro f g h
    apply subst_bea_injective
    rw [← substBlockEsymmAlgHom_apply_coe, ← substBlockEsymmAlgHom_apply_coe, h]
  · rintro ⟨g, hg⟩
    obtain ⟨f, hf⟩ := exists_subst_bea_eq (g := g) fun σ => hg σ
    exact ⟨f, Subtype.ext (by rw [substBlockEsymmAlgHom_apply_coe, hf])⟩

/-- The algebra of blockwise symmetric formal power series, fixed under
independent permutations of the variables in each block, is isomorphic
to the full formal power series ring. The inverse map substitutes the
elementary symmetric functions of each block. -/
public def mvPowerSeriesBlockFixedEquiv :
    letI := blockPermMulSemiringAction k m rs
    letI := blockPermSMulCommClass k m rs
    (FixedPoints.subalgebra k (MvPowerSeries (Fin (∑ j, rs j)) k)
        (∀ j, Equiv.Perm (Fin (rs j))))
      ≃ₐ[k] MvPowerSeries (Fin (∑ j, rs j)) k :=
  letI := blockPermMulSemiringAction k m rs
  letI := blockPermSMulCommClass k m rs
  (AlgEquiv.ofBijective (substBlockEsymmAlgHom k m rs)
    (substBlockEsymmAlgHom_bijective k m rs)).symm

/-- The inverse of the blockwise fixed-point equivalence substitutes,
for each variable, the corresponding block elementary symmetric
function. -/
public theorem mvPowerSeriesBlockFixedEquiv_symm_apply_coe (f : MvPowerSeries (Fin (∑ j, rs j)) k) :
    letI := blockPermMulSemiringAction k m rs
    letI := blockPermSMulCommClass k m rs
    (((mvPowerSeriesBlockFixedEquiv k m rs).symm f : _) : MvPowerSeries _ k)
      = MvPowerSeries.subst (bea k m rs) f := by
  rw [mvPowerSeriesBlockFixedEquiv, AlgEquiv.symm_symm]
  exact substBlockEsymmAlgHom_apply_coe k m rs f

end MvPowerSeries

end
