/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean` and
`P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.UnitsModPowersEigenspace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# The `ω²` eigenspace of the units of `ℚ(ζ_p)` modulo `p`-th powers

For a prime `p ≥ 5`, `Stickelberger.finrank_unitsOmegaEigenspace_two` shows that the `ω²`
eigenspace `Stickelberger.unitsOmegaEigenspace p 2` of `E / E ^ p`, where `E = 𝓞 (ℚ(ζ_p))ˣ`
with the Galois action `Stickelberger.unitsGalAction`, has dimension 1 over `ZMod p`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Graduate Texts in Mathematics
  83, Springer, 1997.
* S. Lang, *Cyclotomic Fields I and II*, Graduate Texts in Mathematics 121, Springer, 1990.

The statement is the `ω²` case of the standard description of the units of `ℚ(ζ_p)` modulo
`p`-th powers as a Galois module; we know of no numbered result of exactly this form in these
sources. It is derived here directly: Dirichlet's unit theorem and the `p`-torsion of `E` give
`dim E / E ^ p = (p - 1) / 2`, the trace of each `unitsGalAction p d` is computed from the
infinite places it fixes, and the trace of the projector `Stickelberger.omegaIdempotent` with
`i = 2` is then `1` in `ZMod p`, which pins the dimension of its range.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace W2Units

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open Module

section General

variable (K : Type*) [Field K] [NumberField K]

private scoped instance : CommGroup ((𝓞 K)ˣ ⧸ torsion K) :=
  QuotientGroup.Quotient.commGroup _

private scoped instance : AddCommGroup (Additive ((𝓞 K)ˣ ⧸ torsion K)) :=
  Additive.addCommGroup

private scoped instance : Module ℤ (Additive ((𝓞 K)ˣ ⧸ torsion K)) :=
  AddCommGroup.toIntModule _

private def unitsMap (σ : K ≃ₐ[ℚ] K) : (𝓞 K)ˣ →* (𝓞 K)ˣ :=
  Units.map ((galRestrict ℤ ℚ K (𝓞 K) σ).toRingEquiv.toRingHom.toMonoidHom)

private lemma unitsMap_coe (σ : K ≃ₐ[ℚ] K) (u : (𝓞 K)ˣ) :
    ((unitsMap K σ u : 𝓞 K) : K) = σ ((u : 𝓞 K) : K) := by
  simpa [unitsMap] using algebraMap_galRestrict_apply ℤ σ (u : 𝓞 K)

private lemma unitsMap_torsion_le (σ : K ≃ₐ[ℚ] K) :
    torsion K ≤ (torsion K).comap (unitsMap K σ) := by
  intro t ht
  rw [Subgroup.mem_comap]
  rw [torsion, CommGroup.mem_torsion] at ht ⊢
  exact MonoidHom.isOfFinOrder _ ht

private def quotMap (σ : K ≃ₐ[ℚ] K) : Additive ((𝓞 K)ˣ ⧸ torsion K) →+ Additive ((𝓞 K)ˣ ⧸ torsion K)
    :=
  MonoidHom.toAdditive
    (QuotientGroup.map (torsion K) (torsion K) (unitsMap K σ) (unitsMap_torsion_le K σ))

private lemma quotMap_mk (σ : K ≃ₐ[ℚ] K) (u : (𝓞 K)ˣ) :
    quotMap K σ (Additive.ofMul ((QuotientGroup.mk u : (𝓞 K)ˣ ⧸ torsion K))) =
      Additive.ofMul (QuotientGroup.mk (unitsMap K σ u)) := rfl

set_option backward.isDefEq.respectTransparency false in

private def quotMapLin (σ : K ≃ₐ[ℚ] K) : Additive ((𝓞 K)ˣ ⧸ torsion K) →ₗ[ℤ] Additive ((𝓞 K)ˣ ⧸
    torsion K) :=
  (quotMap K σ).toIntLinearMap

private lemma quotMapLin_apply (σ : K ≃ₐ[ℚ] K) (x : Additive ((𝓞 K)ˣ ⧸ torsion K)) :
    quotMapLin K σ x = quotMap K σ x := rfl

private def logFull : Additive ((𝓞 K)ˣ) →+ (InfinitePlace K → ℝ) where
  toFun x w := mult w * Real.log (w (x.toMul : K))
  map_zero' := by
    funext w
    simp
  map_add' x y := by
    funext w
    simp only [toMul_add, Units.val_mul, Pi.add_apply, map_mul]
    have hx : w (algebraMap (𝓞 K) K (x.toMul : 𝓞 K)) ≠ 0 :=
      ne_of_gt (pos_iff.mpr (by simp))
    have hy : w (algebraMap (𝓞 K) K (y.toMul : 𝓞 K)) ≠ 0 :=
      ne_of_gt (pos_iff.mpr (by simp))
    rw [Real.log_mul hx hy, mul_add]

omit [NumberField K] in
@[scoped simp] private lemma logFull_apply (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    logFull K (Additive.ofMul u) w = mult w * Real.log (w (u : K)) := rfl

private lemma sum_logFull (x : Additive ((𝓞 K)ˣ)) : ∑ w, logFull K x w = 0 :=
  sum_mult_mul_log x.toMul

private lemma logFull_eq_zero_iff {u : (𝓞 K)ˣ} :
    logFull K (Additive.ofMul u) = 0 ↔ u ∈ torsion K := by
  constructor
  · intro h
    refine (logEmbedding_eq_zero_iff (K := K)).mp ?_
    funext w
    exact congrFun h w.1
  · intro h
    funext w
    have hw : w ((u : 𝓞 K) : K) = 1 := (mem_torsion K).mp h w
    simp [logFull_apply, hw]

private def logQuot : Additive ((𝓞 K)ˣ ⧸ torsion K) →+ (InfinitePlace K → ℝ) :=
  MonoidHom.toAdditiveLeft <|
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight (logFull K))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext u
        rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one,
          ← logFull_eq_zero_iff (K := K)])).toMonoidHom

@[scoped simp] private lemma logQuot_mk (u : (𝓞 K)ˣ) :
    logQuot K (Additive.ofMul ((QuotientGroup.mk u : (𝓞 K)ˣ ⧸ torsion K))) =
      logFull K (Additive.ofMul u) := rfl

omit [NumberField K] in
private lemma logQuot_surjective_rep (x : Additive ((𝓞 K)ˣ ⧸ torsion K)) :
    ∃ u : (𝓞 K)ˣ,
      x = Additive.ofMul ((QuotientGroup.mk u : (𝓞 K)ˣ ⧸ torsion K)) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (x.toMul)
  refine ⟨u, ?_⟩
  rw [hu]
  exact (ofMul_toMul x).symm

private def permL (σ : K ≃ₐ[ℚ] K) : (InfinitePlace K → ℝ) →ₗ[ℝ] (InfinitePlace K → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun w => σ⁻¹ • w)

private lemma mult_smul' (σ : K ≃ₐ[ℚ] K) (w : InfinitePlace K) : mult (σ • w) = mult w := by
  classical
  simp only [mult]
  exact if_congr isReal_smul_iff rfl rfl

private lemma logFull_unitsMap (σ : K ≃ₐ[ℚ] K) (u : (𝓞 K)ˣ) :
    logFull K (Additive.ofMul (unitsMap K σ u)) = permL K σ (logFull K (Additive.ofMul u)) := by
  funext w
  simp only [permL, LinearMap.funLeft_apply, logFull_apply, unitsMap_coe]
  have h1 : (σ⁻¹ • w) ((u : 𝓞 K) : K) = w (σ ((u : 𝓞 K) : K)) := by
    rw [NumberField.InfinitePlace.smul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  rw [mult_smul' K σ⁻¹ w, h1]

private lemma logQuot_quotMap (σ : K ≃ₐ[ℚ] K) (x : Additive ((𝓞 K)ˣ ⧸ torsion K)) :
    logQuot K (quotMap K σ x) = permL K σ (logQuot K x) := by
  obtain ⟨u, rfl⟩ := logQuot_surjective_rep K x
  rw [quotMap_mk, logQuot_mk, logQuot_mk, logFull_unitsMap]

private def vFam : Fin (rank K) → (InfinitePlace K → ℝ) := fun i => logQuot K (basisModTorsion K i)

private def restr : (InfinitePlace K → ℝ) →ₗ[ℝ] logSpace K :=
  LinearMap.funLeft ℝ ℝ (Subtype.val : {w : InfinitePlace K // w ≠ w₀} → InfinitePlace K)

private lemma restr_logFull (x : Additive ((𝓞 K)ˣ)) :
    restr K (logFull K x) = logEmbedding K x := rfl

private lemma restr_vFam (i : Fin (rank K)) :
    restr K (vFam K i) = (basisUnitLattice K i : logSpace K) := by
  obtain ⟨u, hu⟩ := logQuot_surjective_rep K (basisModTorsion K i)
  rw [vFam, hu, logQuot_mk, restr_logFull, basisUnitLattice, Basis.map_apply, hu,
    logEmbeddingEquiv_apply]

private lemma span_restr_vFam :
    Submodule.span ℝ (Set.range ((restr K) ∘ (vFam K))) = ⊤ := by
  rw [← unitLattice_span_eq_top (K := K)]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    rw [Function.comp_apply, restr_vFam]
    exact Submodule.subset_span (basisUnitLattice K i).2
  · rw [Submodule.span_le]
    intro y hy
    set z : unitLattice K := ⟨y, hy⟩ with hzdef
    have hz : y = ((∑ i, (basisUnitLattice K).repr z i • basisUnitLattice K i :
        unitLattice K) : logSpace K) := by
      rw [(basisUnitLattice K).sum_repr z]
    rw [hz]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine zsmul_mem (Submodule.subset_span ?_) _
    refine Set.mem_range.mpr ⟨i, ?_⟩
    rw [Function.comp_apply, restr_vFam]

private lemma linearIndependent_vFam : LinearIndependent ℝ (vFam K) := by
  classical
  refine LinearIndependent.of_comp (restr K) ?_
  refine linearIndependent_of_top_le_span_of_card_eq_finrank
    (le_of_eq (span_restr_vFam K).symm) ?_
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, rank]

private lemma sum_vFam_eq_zero (i : Fin (rank K)) : ∑ w, vFam K i w = 0 := by
  obtain ⟨u, hu⟩ := logQuot_surjective_rep K (basisModTorsion K i)
  rw [vFam, hu, logQuot_mk]
  exact sum_logFull K _

private abbrev Wv : Submodule ℝ (InfinitePlace K → ℝ) := Submodule.span ℝ (Set.range (vFam K))

private abbrev Lone : Submodule ℝ (InfinitePlace K → ℝ) :=
  Submodule.span ℝ {(fun _ => (1 : ℝ) : InfinitePlace K → ℝ)}

private def sFun : (InfinitePlace K → ℝ) →ₗ[ℝ] ℝ := ∑ w, LinearMap.proj w

private lemma sFun_apply (f : InfinitePlace K → ℝ) : sFun K f = ∑ w, f w := by
  simp [sFun]

private lemma sFun_vanish_Wv {x : InfinitePlace K → ℝ} (hx : x ∈ Wv K) : sFun K x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; rw [sFun_apply]; exact sum_vFam_eq_zero K i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private lemma isCompl_Wv_Lone : IsCompl (Wv K) (Lone K) := by
  have hcard : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  have hdisj : Disjoint (Wv K) (Lone K) := by
    rw [Submodule.disjoint_def]
    intro x hxW hxL
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxL
    have h0 := sFun_vanish_Wv K hxW
    rw [map_smul, sFun_apply] at h0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with hc | hc
    · rw [hc, zero_smul]
    · exact absurd hc (Nat.cast_ne_zero.mpr hcard.ne')
  have hone : (fun _ => (1 : ℝ) : InfinitePlace K → ℝ) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary _)
    norm_num at this
  refine ⟨hdisj, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Wv K) (Lone K)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero] at hsum
  have hWv : Module.finrank ℝ (Wv K) = rank K := by
    rw [Wv, finrank_span_eq_card (linearIndependent_vFam K), Fintype.card_fin]
  have hLone : Module.finrank ℝ (Lone K) = 1 := by
    rw [Lone, finrank_span_singleton hone]
  rw [hWv, hLone] at hsum
  rw [hsum, Module.finrank_fintype_fun_eq_card, rank]
  omega

private lemma permL_one_const (σ : K ≃ₐ[ℚ] K) :
    permL K σ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := rfl

private lemma logQuot_mem_Wv (x : Additive ((𝓞 K)ˣ ⧸ torsion K)) : logQuot K x ∈ Wv K := by
  have hx := (basisModTorsion K).sum_repr x
  rw [← hx, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_zsmul]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

private lemma permL_mem_Wv (σ : K ≃ₐ[ℚ] K) {x : InfinitePlace K → ℝ} (hx : x ∈ Wv K) :
    permL K σ x ∈ Wv K := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    rw [show vFam K i = logQuot K (basisModTorsion K i) from rfl, ← logQuot_quotMap]
    exact logQuot_mem_Wv K _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private lemma permL_mem_Lone (σ : K ≃ₐ[ℚ] K) {_x : InfinitePlace K → ℝ} (hx : _x ∈ Lone K) :
    permL K σ _x ∈ Lone K := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, permL_one_const]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma one_ne_zero' : (fun _ => (1 : ℝ) : InfinitePlace K → ℝ) ≠ 0 := by
  intro h
  have := congrFun h (Classical.arbitrary _)
  norm_num at this

private lemma finrank_Lone : Module.finrank ℝ (Lone K) = 1 := by
  rw [Lone, finrank_span_singleton (one_ne_zero' K)]

private lemma trace_funLeft (g : InfinitePlace K → InfinitePlace K) :
    LinearMap.trace ℝ (InfinitePlace K → ℝ) (LinearMap.funLeft ℝ ℝ g) =
      Nat.card {w // g w = w} := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (InfinitePlace K)), Matrix.trace]
  have hdiag : ∀ i, (LinearMap.toMatrix (Pi.basisFun ℝ (InfinitePlace K))
      (Pi.basisFun ℝ (InfinitePlace K)) (LinearMap.funLeft ℝ ℝ g)).diag i =
      if g i = i then 1 else 0 := by
    intro i
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      LinearMap.funLeft_apply, Pi.basisFun_apply]
    simp [Pi.single_apply]
  rw [Finset.sum_congr rfl fun i _ => hdiag i, Finset.sum_boole]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma trace_eq_trace_restrict_add_trace_restrict
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : IsCompl p q) (f : M →ₗ[R] M)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q)
    [Module.Finite R p] [Module.Free R p] [Module.Finite R q] [Module.Free R q] :
    LinearMap.trace R M f =
      LinearMap.trace R p (f.restrict hp) + LinearMap.trace R q (f.restrict hq) := by
  have key : (Submodule.prodEquivOfIsCompl p q h).symm.conj f =
      LinearMap.prodMap (f.restrict hp) (f.restrict hq) := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_symm]
    rw [LinearEquiv.symm_apply_eq]
    rw [LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_prodEquivOfIsCompl', map_add]
    rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply]
  calc LinearMap.trace R M f
      = LinearMap.trace R (p × q) ((Submodule.prodEquivOfIsCompl p q h).symm.conj f) :=
        (LinearMap.trace_conj' f _).symm
    _ = _ := by rw [key, LinearMap.trace_prodMap']

private lemma permL_vFam_eq (σ : K ≃ₐ[ℚ] K) (j : Fin (rank K)) :
    permL K σ (vFam K j) =
      ∑ i, ((LinearMap.toMatrix (basisModTorsion K) (basisModTorsion K)
        (quotMapLin K σ)) i j : ℝ) • vFam K i := by
  have h0 : permL K σ (vFam K j) = logQuot K (quotMapLin K σ (basisModTorsion K j)) := by
    rw [quotMapLin_apply, show vFam K j = logQuot K (basisModTorsion K j) from rfl,
      logQuot_quotMap]
  rw [h0]
  conv_lhs => rw [← (basisModTorsion K).sum_repr (quotMapLin K σ (basisModTorsion K j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, LinearMap.toMatrix_apply]
  exact (Int.cast_smul_eq_zsmul ℝ _ _).symm

private lemma trace_restrict_Lone (σ : K ≃ₐ[ℚ] K) :
    LinearMap.trace ℝ (Lone K)
      ((permL K σ).restrict (fun _x hx => permL_mem_Lone K σ hx)) = 1 := by
  have hid : (permL K σ).restrict (fun _x hx => permL_mem_Lone K σ hx) = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨_x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq, map_smul, permL_one_const]
  rw [hid, LinearMap.trace_id, finrank_Lone]
  norm_num

private lemma trace_restrict_Wv (σ : K ≃ₐ[ℚ] K) :
    LinearMap.trace ℝ (Wv K)
      ((permL K σ).restrict (fun _x hx => permL_mem_Wv K σ hx)) =
      ((LinearMap.toMatrix (basisModTorsion K) (basisModTorsion K)
        (quotMapLin K σ)).trace : ℝ) := by
  classical
  set A := LinearMap.toMatrix (basisModTorsion K) (basisModTorsion K) (quotMapLin K σ)
    with hA
  set bW : Basis (Fin (rank K)) ℝ (Wv K) :=
    (Basis.span (linearIndependent_vFam K) : _) with hbW
  have hcoe : ∀ j, (bW j : InfinitePlace K → ℝ) = vFam K j := by
    intro j
    rw [hbW]
    exact congrArg Subtype.val (Basis.span_apply (linearIndependent_vFam K) j)
  have hW : ∀ j, ((permL K σ).restrict (fun _x hx => permL_mem_Wv K σ hx)) (bW j) =
      ∑ k, (A k j : ℝ) • bW k := by
    intro j
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, hcoe, permL_vFam_eq]
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => by rw [SetLike.val_smul, hcoe]
  have hmat : LinearMap.toMatrix bW bW
      ((permL K σ).restrict (fun _x hx => permL_mem_Wv K σ hx)) =
      A.map (Int.cast : ℤ → ℝ) := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hW j, map_sum]
    simp [Basis.repr_self, Finsupp.single_apply]
  rw [LinearMap.trace_eq_matrix_trace ℝ bW, hmat, Matrix.trace, Matrix.trace]
  push_cast
  rfl

private theorem trace_quotMap_eq (σ : K ≃ₐ[ℚ] K) :
    LinearMap.trace ℤ (Additive ((𝓞 K)ˣ ⧸ torsion K)) (quotMapLin K σ) =
      (Nat.card {w : InfinitePlace K // σ • w = w} : ℤ) - 1 := by
  classical
  set A := LinearMap.toMatrix (basisModTorsion K) (basisModTorsion K) (quotMapLin K σ)
    with hA
  have h1 : LinearMap.trace ℤ (Additive ((𝓞 K)ˣ ⧸ torsion K)) (quotMapLin K σ) = A.trace := by
    rw [hA]
    exact LinearMap.trace_eq_matrix_trace ℤ (basisModTorsion K) _
  have h2 : LinearMap.trace ℝ (InfinitePlace K → ℝ) (permL K σ) =
      (Nat.card {w : InfinitePlace K // σ • w = w} : ℝ) := by
    rw [show permL K σ = LinearMap.funLeft ℝ ℝ (fun w => σ⁻¹ • w) from rfl, trace_funLeft]
    congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun w => ?_
    rw [inv_smul_eq_iff, eq_comm]
  have h3 := trace_eq_trace_restrict_add_trace_restrict (isCompl_Wv_Lone K) (permL K σ)
    (fun _x hx => permL_mem_Wv K σ hx) (fun _x hx => permL_mem_Lone K σ hx)
  rw [trace_restrict_Wv, trace_restrict_Lone, h2, ← hA] at h3
  rw [h1]
  have h4 : ((A.trace : ℤ) : ℝ) =
      ((Nat.card {w : InfinitePlace K // σ • w = w} : ℤ) : ℝ) - 1 := by
    push_cast
    rw [h3]
    ring
  exact_mod_cast h4

end General

section Cyclo

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

private lemma neZero_p' : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] neZero_p'

private lemma neg_one_inv' : (-1 : (ZMod p)ˣ)⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (by simp)

private lemma pow_natCast_neg_one {z : ℂ} (hz : IsPrimitiveRoot z p)
    {n : ℕ} (hn : (n : ZMod p) = -1) : z ^ n = z⁻¹ := by
  have hd : p ∣ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hn]
    ring
  obtain ⟨k, hk⟩ := hd
  have h1 : z ^ (n + 1) = 1 := by rw [hk, pow_mul, hz.pow_eq_one, one_pow]
  rw [pow_succ] at h1
  exact eq_inv_of_mul_eq_one_left h1

private lemma natCast_eq_neg_one_of_pow {z : ℂ} (hz : IsPrimitiveRoot z p) (hz0 : z ≠ 0)
    {n : ℕ} (hpow : z ^ n = z⁻¹) : (n : ZMod p) = -1 := by
  have h1 : z ^ (n + 1) = 1 := by rw [pow_succ, hpow, inv_mul_cancel₀ hz0]
  have h2 := (hz.pow_eq_one_iff_dvd _).mp h1
  have h0 : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

open IsCyclotomicExtension.Rat in
private lemma symm_symm_apply_zeta (d : (ZMod p)ˣ) :
    ((galEquivZMod p K).symm d).symm (IsCyclotomicExtension.zeta p ℚ K) =
      (IsCyclotomicExtension.zeta p ℚ K) ^ ((d⁻¹ : (ZMod p)ˣ) : ZMod p).val := by
  have h1 : ((galEquivZMod p K).symm d).symm = (galEquivZMod p K).symm d⁻¹ := by
    rw [← AlgEquiv.aut_inv, ← map_inv]
  rw [h1]
  have h2 := galEquivZMod_apply_of_pow_eq p K ((galEquivZMod p K).symm d⁻¹)
    ((IsCyclotomicExtension.zeta_spec p ℚ K).pow_eq_one)
  rwa [MulEquiv.apply_symm_apply] at h2

open IsCyclotomicExtension.Rat in
private theorem smul_infinitePlace_eq_self_iff (_hp : 2 < p) (d : (ZMod p)ˣ) (w : InfinitePlace K) :
    (galEquivZMod p K).symm d • w = w ↔ (d = 1 ∨ d = -1) := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hzprim : IsPrimitiveRoot (w.embedding (IsCyclotomicExtension.zeta p ℚ K)) p :=
    hζ.map_of_injective w.embedding.injective
  have hz0 : w.embedding (IsCyclotomicExtension.zeta p ℚ K) ≠ 0 := by
    intro h0
    have := hzprim.pow_eq_one
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at this
    exact zero_ne_one this
  have hznorm : ‖w.embedding (IsCyclotomicExtension.zeta p ℚ K)‖ = 1 := by
    refine Complex.norm_eq_one_of_pow_eq_one ?_ (Fact.out : p.Prime).ne_zero
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have hconj : (starRingEnd ℂ) (w.embedding (IsCyclotomicExtension.zeta p ℚ K)) =
      (w.embedding (IsCyclotomicExtension.zeta p ℚ K))⁻¹ :=
    (Complex.inv_eq_conj hznorm).symm
  constructor
  · intro hw
    rw [← mk_embedding w, smul_mk] at hw
    rcases mk_eq_iff.mp hw with h | h
    · left
      have hσ1 : (galEquivZMod p K).symm d = 1 := by
        have hsymm : ((galEquivZMod p K).symm d).symm = 1 := by
          apply AlgEquiv.ext
          intro x
          exact w.embedding.injective (RingHom.congr_fun h x)
        calc (galEquivZMod p K).symm d
            = ((galEquivZMod p K).symm d).symm.symm := (AlgEquiv.symm_symm _).symm
          _ = (1 : K ≃ₐ[ℚ] K).symm := by rw [hsymm]
          _ = 1 := rfl
      have hd1 : d = galEquivZMod p K ((galEquivZMod p K).symm d) :=
        (MulEquiv.apply_symm_apply _ d).symm
      rw [hσ1, map_one] at hd1
      exact hd1
    · right
      have heval : w.embedding (((galEquivZMod p K).symm d).symm
          (IsCyclotomicExtension.zeta p ℚ K)) =
          (w.embedding (IsCyclotomicExtension.zeta p ℚ K))⁻¹ := by
        have h2 := congrArg (starRingEnd ℂ)
          (RingHom.congr_fun h (IsCyclotomicExtension.zeta p ℚ K))
        rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj] at h2
        rw [RingHom.coe_comp, Function.comp_apply] at h2
        exact h2.trans hconj
      rw [symm_symm_apply_zeta, map_pow] at heval
      have hcast : (((((d⁻¹ : (ZMod p)ˣ) : ZMod p)).val : ZMod p)) = -1 :=
        natCast_eq_neg_one_of_pow p hzprim hz0 heval
      rw [ZMod.natCast_val, ZMod.cast_id] at hcast
      have hinv : d⁻¹ = (-1 : (ZMod p)ˣ) := by
        apply Units.ext
        rw [hcast]
        simp
      rw [← inv_inv d, hinv, neg_one_inv']
  · intro hd
    rcases hd with rfl | rfl
    · rw [map_one]
      exact one_smul _ w
    · rw [← mk_embedding w, smul_mk, mk_eq_iff]
      right
      have hgen : w.embedding (((galEquivZMod p K).symm (-1)).symm
          (IsCyclotomicExtension.zeta p ℚ K)) =
          ComplexEmbedding.conjugate w.embedding (IsCyclotomicExtension.zeta p ℚ K) := by
        rw [symm_symm_apply_zeta, map_pow, ComplexEmbedding.conjugate_coe_eq, hconj]
        refine pow_natCast_neg_one p hzprim ?_
        rw [ZMod.natCast_val, ZMod.cast_id, neg_one_inv']
        simp
      have h1 : RingHom.toRatAlgHom
          (w.embedding.comp ↑(((galEquivZMod p K).symm (-1)).symm)) =
          RingHom.toRatAlgHom (ComplexEmbedding.conjugate w.embedding) := by
        apply PowerBasis.algHom_ext (hζ.powerBasis ℚ)
        rw [IsPrimitiveRoot.powerBasis_gen]
        exact hgen
      have h2 : w.embedding.comp ↑(((galEquivZMod p K).symm (-1)).symm) =
          ComplexEmbedding.conjugate w.embedding := congrArg AlgHom.toRingHom h1
      rw [h2]
      exact star_star w.embedding

open IsCyclotomicExtension.Rat in
private theorem card_fixedPlaces (hp : 2 < p) (d : (ZMod p)ˣ) :
    Nat.card {w : InfinitePlace K // (galEquivZMod p K).symm d • w = w} =
      if d = 1 ∨ d = -1 then p.totient / 2 else 0 := by
  split_ifs with hd
  · rw [Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun w => (smul_infinitePlace_eq_self_iff p K hp d w).mpr hd))]
    rw [Nat.card_eq_fintype_card]
    have h1 := card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h2 : nrRealPlaces K = 0 := nrRealPlaces_eq_zero K hp
    have h3 : nrComplexPlaces K = p.totient / 2 := nrComplexPlaces_eq_totient_div_two p K
    omega
  · have he : IsEmpty {w : InfinitePlace K // (galEquivZMod p K).symm d • w = w} := by
      refine ⟨fun x => hd ?_⟩
      exact (smul_infinitePlace_eq_self_iff p K hp d x.1).mp x.2
    have := he
    exact Nat.card_of_isEmpty

end Cyclo

end W2Units
open scoped W2Units

namespace Aux1Bridge

open NumberField NumberField.Units Stickelberger W2Units

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]

private noncomputable def vMap (σ : K ≃ₐ[ℚ] K) :
    ModN (Additive (𝓞 K)ˣ) p →ₗ[ZMod p] ModN (Additive (𝓞 K)ˣ) p :=
  Stickelberger.modNEnd p (MonoidHom.toAdditive (unitsMap K σ))

private lemma vMap_proj (σ : K ≃ₐ[ℚ] K) (u : (𝓞 K)ˣ) :
    vMap p K σ (ModN.mkQ p (Additive.ofMul u)) =
      ModN.mkQ p (Additive.ofMul (unitsMap K σ u)) := rfl

private theorem exists_basis (hdiv : p ∣ torsionOrder K) (t : torsion K)
    (ht : ∀ x : torsion K, x ∈ Subgroup.zpowers t) :
    ∃ b : Module.Basis (Option (Fin (rank K))) (ZMod p) (ModN (Additive (𝓞 K)ˣ) p),
      b none = ModN.mkQ p (Additive.ofMul (t : (𝓞 K)ˣ)) ∧
      ∀ i, b (some i) = ModN.mkQ p (Additive.ofMul (fundSystem K i)) := by
  classical
  have hord : orderOf t = torsionOrder K := by
    rw [torsionOrder]
    exact orderOf_eq_card_of_forall_mem_zpowers ht
  let a : Option (Fin (rank K)) → Additive (𝓞 K)ˣ := fun o =>
    o.elim (Additive.ofMul ((t : (𝓞 K)ˣ))) (fun i => Additive.ofMul (fundSystem K i))
  let v : Option (Fin (rank K)) → ModN (Additive (𝓞 K)ˣ) p := fun o => ModN.mkQ p (a o)
  have ha_none : Additive.toMul (a none) = (t : (𝓞 K)ˣ) := rfl
  have ha_some : ∀ i, Additive.toMul (a (some i)) = fundSystem K i := fun i => rfl
  have hli : LinearIndependent (ZMod p) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∑ o, g o • v o = ModN.mkQ p (∑ o, (g o).val • a o) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [key, ModN.mkQ_eq_zero_iff] at hg
    obtain ⟨b, hb⟩ := hg
    set u : (𝓞 K)ˣ := Additive.toMul b with hu_def
    have hb' : u ^ p = (t : (𝓞 K)ˣ) ^ (g none).val *
        ∏ i, fundSystem K i ^ (((g (some i)).val : ℕ) : ℤ) := by
      have := congrArg Additive.toMul hb
      rw [toMul_nsmul, toMul_sum, Fintype.prod_option] at this
      simp only [toMul_nsmul, ha_none, ha_some, zpow_natCast] at this ⊢
      exact this
    obtain ⟨⟨ζu, eu⟩, hu, -⟩ := exist_unique_eq_mul_prod K u
    have h1 : u ^ p = ((⟨t ^ (g none).val, fun i => (((g (some i)).val : ℕ) : ℤ)⟩ :
        torsion K × (Fin (rank K) → ℤ))).1 * ∏ i, fundSystem K i ^
          ((⟨t ^ (g none).val, fun i => (((g (some i)).val : ℕ) : ℤ)⟩ :
            torsion K × (Fin (rank K) → ℤ))).2 i := by
      simpa only [Subgroup.coe_pow] using hb'
    have h2 : u ^ p = ((⟨ζu ^ p, fun i => (p : ℤ) * eu i⟩ :
        torsion K × (Fin (rank K) → ℤ))).1 * ∏ i, fundSystem K i ^
          ((⟨ζu ^ p, fun i => (p : ℤ) * eu i⟩ : torsion K × (Fin (rank K) → ℤ))).2 i := by
      simp only [Subgroup.coe_pow]
      conv_lhs => rw [hu]
      rw [mul_pow, ← Finset.prod_pow]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
    have huniq := (exist_unique_eq_mul_prod K (u ^ p)).unique h1 h2
    simp only [Prod.mk.injEq] at huniq
    obtain ⟨htor, hfun⟩ := huniq
    intro o
    cases o with
    | some i =>
      have hi := congrFun hfun i
      rw [← ZMod.natCast_zmod_val (g (some i)), ← Int.cast_natCast, hi]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    | none =>
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζu)
      have : t ^ ((g none).val : ℤ) = t ^ (m * p) := by
        rw [zpow_natCast, htor, ← hm, ← zpow_natCast, ← zpow_mul]
      rw [zpow_eq_zpow_iff_modEq, hord] at this
      have hmod := this.of_dvd (Int.natCast_dvd_natCast.mpr hdiv)
      rw [← ZMod.natCast_zmod_val (g none), ← Int.cast_natCast,
        (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod]
      push_cast
      rw [ZMod.natCast_self, mul_zero]
  have hsp : ⊤ ≤ Submodule.span (ZMod p) (Set.range v) := by
    rintro x -
    obtain ⟨y, rfl⟩ := ModN.mkQ_surjective p x
    obtain ⟨⟨ζu, eu⟩, hu, -⟩ := exist_unique_eq_mul_prod K (Additive.toMul y)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζu)
    have hy : y = m • a none + ∑ i, eu i • a (some i) := by
      apply Additive.toMul.injective
      rw [toMul_add, toMul_zsmul, toMul_sum, ha_none]
      simp only [toMul_zsmul, ha_some]
      rw [hu, ← hm, Subgroup.coe_zpow]
    rw [hy, map_add, map_zsmul, map_sum]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
    · rw [← Int.cast_smul_eq_zsmul (ZMod p)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)
    · rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod p)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨some i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, ?_, fun i => ?_⟩
  · rw [Module.Basis.mk_apply]; rfl
  · rw [Module.Basis.mk_apply]; rfl

private theorem finrank_modP_units (hdiv : p ∣ torsionOrder K) :
    Module.finrank (ZMod p) (ModN (Additive (𝓞 K)ˣ) p) = rank K + 1 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := torsion K)
  obtain ⟨b, -, -⟩ := exists_basis p K hdiv t ht
  rw [Module.finrank_eq_card_basis b, Fintype.card_option, Fintype.card_fin]

private theorem trace_vMap (hdiv : p ∣ torsionOrder K) (σ : K ≃ₐ[ℚ] K) (n : ℕ)
    (hσ : ∀ x : 𝓞 K, x ^ p = 1 → galRestrict ℤ ℚ K (𝓞 K) σ x = x ^ n) :
    LinearMap.trace (ZMod p) _ (vMap p K σ) =
      (n : ZMod p) + ((LinearMap.trace ℤ _ (quotMapLin K σ) : ℤ) : ZMod p) := by
  classical
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := torsion K)
  have hord : orderOf t = torsionOrder K := by
    rw [torsionOrder]
    exact orderOf_eq_card_of_forall_mem_zpowers ht
  obtain ⟨b, hb_none, hb_some⟩ := exists_basis p K hdiv t ht
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp
    (ht ⟨unitsMap K σ (t : (𝓞 K)ˣ), unitsMap_torsion_le K σ t.2⟩)
  have he' : unitsMap K σ (t : (𝓞 K)ˣ) = (t : (𝓞 K)ˣ) ^ e := by
    have := congrArg (fun x : torsion K => (x : (𝓞 K)ˣ)) he
    simpa only [Subgroup.coe_zpow] using this.symm
  obtain ⟨q, hq⟩ := hdiv
  have hqpos : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp [torsionOrder_ne_zero K] at hq)
  have he_n : (e : ZMod p) = (n : ZMod p) := by
    set y : (𝓞 K)ˣ := (t : (𝓞 K)ˣ) ^ q with hy
    have hyp : (y : 𝓞 K) ^ p = 1 := by
      rw [hy, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← hq, ← hord,
        ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have h1 : unitsMap K σ y = y ^ n := by
      ext
      rw [Units.val_pow_eq_pow_val, ← hσ _ hyp]
      rfl
    have h2 : unitsMap K σ y = (t : (𝓞 K)ˣ) ^ ((q : ℤ) * e) := by
      rw [hy, map_pow, he', ← zpow_natCast, ← zpow_mul, mul_comm]
    have h3 : (t : (𝓞 K)ˣ) ^ ((q : ℤ) * e) = (t : (𝓞 K)ˣ) ^ ((q : ℤ) * n) := by
      rw [← h2, h1, hy, ← pow_mul, ← zpow_natCast, Nat.cast_mul]
    rw [zpow_eq_zpow_iff_modEq, Subgroup.orderOf_coe, hord, hq, Nat.cast_mul,
      mul_comm (p : ℤ) (q : ℤ)] at h3
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hmod : e ≡ (n : ℤ) [ZMOD (p : ℤ)] := Int.ModEq.mul_left_cancel' hq0 h3
    rw [← Int.cast_natCast n]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
  have row_none : b.repr (vMap p K σ (b none)) none = n := by
    rw [hb_none, vMap_proj, he', ofMul_zpow, map_zsmul, ← hb_none,
      ← Int.cast_smul_eq_zsmul (ZMod p), map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, he_n]
  have row_some : ∀ i, b.repr (vMap p K σ (b (some i))) (some i) =
      (((basisModTorsion K).repr (quotMapLin K σ (basisModTorsion K i)) i : ℤ) : ZMod p) := by
    intro i
    set w : (𝓞 K)ˣ := unitsMap K σ (fundSystem K i) with hw_def
    obtain ⟨⟨ζw, ew⟩, hw, -⟩ := exist_unique_eq_mul_prod K w
    dsimp only at hw
    have hrepr : ew = (basisModTorsion K).repr (quotMapLin K σ (basisModTorsion K i)) := by
      rw [fun_eq_repr K ζw.2 hw, quotMapLin_apply, ← fundSystem_mk, quotMap_mk]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζw)
    have hζw : (ζw : (𝓞 K)ˣ) = (t : (𝓞 K)ˣ) ^ m := by
      rw [← hm, Subgroup.coe_zpow]
    have hvw : vMap p K σ (b (some i)) =
        (m : ZMod p) • b none + ∑ j, ((ew j : ℤ) : ZMod p) • b (some j) := by
      rw [hb_some, vMap_proj, ← hw_def, hw, hζw, ofMul_mul, ofMul_zpow, ofMul_prod, map_add,
        map_zsmul, map_sum, hb_none, Int.cast_smul_eq_zsmul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ofMul_zpow, map_zsmul, hb_some, Int.cast_smul_eq_zsmul]
    rw [hvw, map_add, map_sum, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Option.some.injEq, reduceCtorEq, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_false,
      zero_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hrepr]
  rw [LinearMap.trace_eq_matrix_trace (ZMod p) b, LinearMap.trace_eq_matrix_trace ℤ
    (basisModTorsion K)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Fintype.sum_option, row_none,
    row_some, Int.cast_sum]

end Aux1Bridge
open scoped W2Units

namespace Aux1Herbrand

open NumberField NumberField.Units Stickelberger
open W2Units Aux1Bridge

variable (p : ℕ) [hp : Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in

private theorem finrank_unitsModN' (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p) = (p - 1) / 2 := by
  have hdiv : p ∣ torsionOrder (CyclotomicField p ℚ) :=
    dvd_torsionOrder_of_isPrimitiveRoot (IsCyclotomicExtension.zeta_spec p ℚ _)
  rw [Aux1Bridge.finrank_modP_units p _ hdiv, rank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (CyclotomicField p ℚ) (by omega : 2 < p),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two p, Nat.totient_prime hp.out]
  omega

set_option backward.isDefEq.respectTransparency false in

private theorem unitsGalAction_eq_vMap (d : (ZMod p)ˣ) :
    unitsGalAction p d = Aux1Bridge.vMap p (CyclotomicField p ℚ)
      ((IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm d) := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := ModN.mkQ_surjective p x
  change unitsEnd p _ (clRingAction p _ d) (ModN.mkQ p (Additive.ofMul (Additive.toMul a))) =
    Aux1Bridge.vMap p (CyclotomicField p ℚ) _ (ModN.mkQ p (Additive.ofMul (Additive.toMul a)))
  rw [unitsEnd_proj, Aux1Bridge.vMap_proj]
  have hu : Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv (Additive.toMul a) =
      unitsMap (CyclotomicField p ℚ)
        ((IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm d)
        (Additive.toMul a) := Units.ext rfl
  rw [hu]

set_option backward.isDefEq.respectTransparency false in

private theorem trace_unitsGalAction' (hp5 : 5 ≤ p) (d : (ZMod p)ˣ) :
    LinearMap.trace (ZMod p) (ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p)
      (unitsGalAction p d) =
      ((d : ZMod p) - 1) + (if d = 1 ∨ d = -1 then (((p - 1) / 2 : ℕ) : ZMod p) else 0) := by
  have hdiv : p ∣ torsionOrder (CyclotomicField p ℚ) :=
    dvd_torsionOrder_of_isPrimitiveRoot (IsCyclotomicExtension.zeta_spec p ℚ _)
  have hσ : ∀ x : 𝓞 (CyclotomicField p ℚ), x ^ p = 1 →
      galRestrict ℤ ℚ (CyclotomicField p ℚ) (𝓞 (CyclotomicField p ℚ))
        ((IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm d) x =
        x ^ (d : ZMod p).val :=
    fun x hx => clRingAction_apply_of_pow_eq p _ d hx
  rw [unitsGalAction_eq_vMap, Aux1Bridge.trace_vMap p _ hdiv _ _ hσ, W2Units.trace_quotMap_eq,
    W2Units.card_fixedPlaces p _ (by omega) d, ZMod.natCast_zmod_val, Nat.totient_prime hp.out,
    Int.cast_sub, Int.cast_one, Int.cast_natCast, Nat.cast_ite, Nat.cast_zero]
  split_ifs <;> ring

end Aux1Herbrand
open scoped W2Units

namespace Aux1Dim

open NumberField Stickelberger Finset

variable (p : ℕ) [hp : Fact p.Prime]

private lemma natCast_natCard_units_zmod : ((Nat.card (ZMod p)ˣ : ℕ) : ZMod p) = -1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out,
    Nat.cast_sub hp.out.one_le, Nat.cast_one, CharP.cast_eq_zero (ZMod p) p, zero_sub]

private lemma sum_units_pow_eq_zero (i : ℕ) (hi : ¬ (p - 1) ∣ i) :
    ∑ d : (ZMod p)ˣ, (d : ZMod p) ^ i = 0 := by
  have h := FiniteField.sum_pow_units (ZMod p) i
  rw [ZMod.card p, ite_eq_right hi] at h
  simpa [Units.val_pow_eq_pow_val] using h

private lemma sum_units_inv_pow_eq_zero (i : ℕ) (hi : ¬ (p - 1) ∣ i) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ i)⁻¹ = 0 := by
  rw [← sum_units_pow_eq_zero p i hi]
  refine Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ) _ _ fun d => ?_
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_pow]

private lemma sum_inv_sq_mul_sub_one (hp5 : 5 ≤ p) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * ((d : ZMod p) - 1) = 0 := by
  have h1 : ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 1)⁻¹ = 0 :=
    sum_units_inv_pow_eq_zero p 1 (by intro h; have := Nat.le_of_dvd one_pos h; omega)
  have h2 : ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ = 0 :=
    sum_units_inv_pow_eq_zero p 2 (by intro h; have := Nat.le_of_dvd two_pos h; omega)
  have : ∀ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * ((d : ZMod p) - 1) =
      ((d : ZMod p) ^ 1)⁻¹ - ((d : ZMod p) ^ 2)⁻¹ := by
    intro d
    have hd : (d : ZMod p) ≠ 0 := Units.ne_zero d
    field_simp
  simp only [this, Finset.sum_sub_distrib, h1, h2, sub_zero]

private lemma sum_inv_sq_mul_indicator (hp5 : 5 ≤ p) (m : ZMod p) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * (if d = 1 ∨ d = -1 then m else 0) = 2 * m := by
  have : Fact (2 < p) := ⟨by omega⟩
  have hne : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    simp only [Units.val_neg, Units.val_one] at this
    exact ZMod.neg_one_ne_one this
  have hsplit : ∀ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * (if d = 1 ∨ d = -1 then m else 0) =
      (if d = 1 then m else 0) + (if d = -1 then m else 0) := by
    intro d
    by_cases h1 : d = 1
    · subst h1; simp [hne.symm]
    · by_cases h2 : d = -1
      · subst h2; simp [hne]
      · simp [h1, h2]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

private lemma trace_omegaIdempotent_two (hp5 : 5 ≤ p) :
    LinearMap.trace (ZMod p) _ (omegaIdempotent p (unitsGalAction p) 2) = 1 := by
  have hm : (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) = -1 := by
    have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
    have h : 2 * ((p - 1) / 2) = p - 1 := by omega
    have : ((2 * ((p - 1) / 2) : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by rw [h]
    push_cast at this
    rw [this, Nat.cast_sub hp.out.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  simp only [omegaIdempotent, map_smul, map_sum, Aux1Herbrand.trace_unitsGalAction' p hp5,
      smul_eq_mul,
    mul_add, Finset.sum_add_distrib, sum_inv_sq_mul_sub_one p hp5,
    sum_inv_sq_mul_indicator p hp5, zero_add, hm, natCast_natCard_units_zmod p]
  rw [inv_neg, inv_one]; ring

private lemma range_omegaIdempotent_two :
    LinearMap.range (omegaIdempotent p (unitsGalAction p) 2) = unitsOmegaEigenspace p 2 := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact isOmegaEigenvector_omegaIdempotent p (unitsGalAction p) 2 x
  · intro x hx
    exact ⟨x, omegaIdempotent_apply_of_isOmegaEigenvector p (unitsGalAction p) hx⟩

private lemma isIdempotentElem_omegaIdempotent_two :
    IsIdempotentElem (omegaIdempotent p (unitsGalAction p) 2) := by
  exact omegaIdempotent_comp_self p (unitsGalAction p) 2

private theorem finrank_unitsOmegaEigenspace_two' (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (unitsOmegaEigenspace p 2) = 1 := by
  have : Module.Finite (ZMod p) (ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p) :=
    Module.finite_of_finrank_pos (by rw [Aux1Herbrand.finrank_unitsModN' p hp5]; omega)
  rw [← range_omegaIdempotent_two p]
  have hproj := LinearMap.IsIdempotentElem.isProj_range _ (isIdempotentElem_omegaIdempotent_two p)
  have htr := LinearMap.IsProj.trace hproj
  rw [trace_omegaIdempotent_two p hp5] at htr
  have hle : Module.finrank (ZMod p)
      (LinearMap.range (omegaIdempotent p (unitsGalAction p) 2)) ≤ (p - 1) / 2 := by
    rw [← Aux1Herbrand.finrank_unitsModN' p hp5]; exact Submodule.finrank_le _
  have hlt : Module.finrank (ZMod p)
      (LinearMap.range (omegaIdempotent p (unitsGalAction p) 2)) < p := by omega
  have hval := congrArg ZMod.val htr
  rw [ZMod.val_one, ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval
  exact hval.symm

end Aux1Dim
open scoped W2Units

namespace Stickelberger

/-- For a prime `p ≥ 5`, the `ω²`-eigenspace of the units of `𝓞 (ℚ(ζ_p))` modulo `p`-th powers
is one-dimensional over `ZMod p`. -/
public theorem finrank_unitsOmegaEigenspace_two (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (unitsOmegaEigenspace p 2) = 1 :=
  Aux1Dim.finrank_unitsOmegaEigenspace_two' p hp5

end Stickelberger
