/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental.lean`
and
`P2M/Sol/S_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental.lean`
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
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Relrank
import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

set_option autoImplicit false

noncomputable section

open IntermediateField Polynomial

private def frobeniusSubfield (M : Type*) [Field M] (p : ℕ) [ExpChar M p] : Subfield M :=
  (frobenius M p).fieldRange

private theorem mem_frobeniusSubfield_iff {M : Type*} [Field M] (p : ℕ) [ExpChar M p] {a : M} :
    a ∈ frobeniusSubfield M p ↔ ∃ b : M, b ^ p = a := by
  simp only [frobeniusSubfield, RingHom.mem_fieldRange, frobenius_def]

private theorem pow_mem_frobeniusSubfield {M : Type*} [Field M] (p : ℕ) [ExpChar M p] (a : M) :
    a ^ p ∈ frobeniusSubfield M p := (mem_frobeniusSubfield_iff p).mpr ⟨a, rfl⟩

private def frobeniusRingEquivRange (M : Type*) [Field M] (p : ℕ) [ExpChar M p] :
    M ≃+* frobeniusSubfield M p :=
  RingEquiv.ofBijective (frobenius M p).rangeRestrict
    ⟨fun _ _ h ↦ (frobenius M p).injective (Subtype.ext_iff.mp h),
      (frobenius M p).rangeRestrict_surjective⟩

private theorem frobeniusRingEquivRange_apply (M : Type*) [Field M] (p : ℕ) [ExpChar M p]
    (a : M) : ((frobeniusRingEquivRange M p a : frobeniusSubfield M p) : M) = a ^ p := rfl

section Transport

variable {E M : Type*} [Field E] [Field M] [Algebra E M] (p : ℕ) [ExpChar E p] [ExpChar M p]

private abbrev frobeniusSubfieldImageInM : Subfield M :=
  (frobeniusSubfield E p).map (algebraMap E M)

omit [ExpChar M p] in
private theorem frobeniusSubfieldImageInM_le_algebraMapRange :
    frobeniusSubfieldImageInM (E := E) (M := M) p ≤ (algebraMap E M).fieldRange :=
  fun _ ⟨a, _, ha⟩ ↦ ⟨a, ha⟩

private theorem frobeniusSubfieldImageInM_le_frobeniusSubfield :
    frobeniusSubfieldImageInM (E := E) (M := M) p ≤ frobeniusSubfield M p := by
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  exact ⟨algebraMap E M b, by simp only [frobenius_def, map_pow]⟩

private theorem comap_frobenius_frobeniusSubfield :
    (frobeniusSubfield M p).comap (frobenius M p) = ⊤ := by
  ext x; constructor
  · intro _; trivial
  · intro _; exact ⟨x, rfl⟩

private theorem comap_frobenius_frobeniusSubfieldImageInM :
    (frobeniusSubfieldImageInM (E := E) (M := M) p).comap (frobenius M p) =
      (algebraMap E M).fieldRange := by
  ext x; constructor
  · rintro ⟨_, ⟨b, rfl⟩, hb⟩
    exact ⟨b, (frobenius M p).injective (by simpa only [frobenius_def, map_pow] using hb)⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e ^ p, ⟨e, rfl⟩, by simp only [frobenius_def, map_pow]⟩

private theorem finrank_algebraMapRange_eq :
    Module.finrank (↥(algebraMap E M).fieldRange) M = Module.finrank E M := by
  have h := Algebra.lift_rank_eq_of_equiv_equiv
    (algebraMap E M).rangeRestrictFieldEquiv (RingEquiv.refl M) (by
      ext e
      rfl)
  simp only [Cardinal.lift_id] at h
  exact congrArg Cardinal.toNat h.symm

private theorem finrank_frobeniusSubfield_eq [FiniteDimensional E M]
    [FiniteDimensional (frobeniusSubfield E p) E] :
    Module.finrank (frobeniusSubfield M p) M = Module.finrank (frobeniusSubfield E p) E := by
  set Mp : Subfield M := frobeniusSubfield M p with hMp
  set Ep' : Subfield M := frobeniusSubfieldImageInM (E := E) (M := M) p with hEp'
  set E' : Subfield M := (algebraMap E M).fieldRange with hE'
  have hfrob : Subfield.relfinrank Ep' Mp = Subfield.relfinrank E' (⊤ : Subfield M) := by
    have h1 := Subfield.relfinrank_comap_comap_eq_relfinrank_of_le (A := Ep') (B := Mp)
      (frobenius M p) (by rw [hMp]; exact le_refl _)
    rw [comap_frobenius_frobeniusSubfield, comap_frobenius_frobeniusSubfieldImageInM] at h1
    exact h1.symm
  have htowerE : Subfield.relfinrank Ep' E' * Subfield.relfinrank E' (⊤ : Subfield M) =
      Subfield.relfinrank Ep' (⊤ : Subfield M) :=
    Subfield.relfinrank_mul_relfinrank
      (frobeniusSubfieldImageInM_le_algebraMapRange p) le_top
  have htowerM : Subfield.relfinrank Ep' Mp * Subfield.relfinrank Mp (⊤ : Subfield M) =
      Subfield.relfinrank Ep' (⊤ : Subfield M) :=
    Subfield.relfinrank_mul_relfinrank
      (frobeniusSubfieldImageInM_le_frobeniusSubfield p) le_top
  have hEp'E' : Subfield.relfinrank Ep' E' = Module.finrank (frobeniusSubfield E p) E := by
    have h1 : E' = (⊤ : Subfield E).map (algebraMap E M) := by
      rw [hE', ← RingHom.fieldRange_eq_map]
    rw [hEp', h1, Subfield.relfinrank_map_map, Subfield.relfinrank_top_right]
  have hMpTop : Subfield.relfinrank Mp (⊤ : Subfield M) =
      Module.finrank (frobeniusSubfield M p) M :=
    Subfield.relfinrank_top_right _
  have hE'pos : 0 < Subfield.relfinrank E' (⊤ : Subfield M) := by
    rw [Subfield.relfinrank_top_right, hE', finrank_algebraMapRange_eq (E := E) (M := M)]
    exact Module.finrank_pos
  have hcancel : Subfield.relfinrank Ep' E' = Subfield.relfinrank Mp (⊤ : Subfield M) := by
    have h := htowerE.trans htowerM.symm
    rw [hfrob, mul_comm (Subfield.relfinrank E' _)] at h
    exact Nat.eq_of_mul_eq_mul_right hE'pos h
  rw [← hMpTop, ← hcancel, hEp'E']

end Transport

section LinearIndependence

variable {M : Type*} [Field M] (p : ℕ) [hp : Fact p.Prime] [CharP M p]

private theorem pDigits_linearIndependent {t : M} (htp : ∀ a : M, a ^ p ≠ t) :
    haveI : ExpChar M p := ExpChar.prime hp.out
    LinearIndependent (frobeniusSubfield M p)
      (fun i : Fin p ↦ (t ^ (i : ℕ) : M)) := by
  haveI : ExpChar M p := ExpChar.prime hp.out

  have htp' : ∀ c : frobeniusSubfield M p, c ^ p ≠
      (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ : frobeniusSubfield M p) := by
    rintro ⟨_, b, rfl⟩ hcp
    refine htp b ((frobenius M p).injective ?_)
    have hcp' := congrArg (fun z : frobeniusSubfield M p ↦ (z : M)) hcp
    push_cast at hcp'
    simpa only [frobenius_def] using hcp'

  have hirr : Irreducible (X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ :
      frobeniusSubfield M p)) :=
    X_pow_sub_C_irreducible_of_prime hp.out htp'

  have hroot : (aeval (R := ↥(frobeniusSubfield M p)) t)
      (X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ : frobeniusSubfield M p)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_self _

  have hmon : (X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ :
      frobeniusSubfield M p)).Monic := monic_X_pow_sub_C _ hp.out.ne_zero

  have hmp : X ^ p - C (⟨t ^ p, pow_mem_frobeniusSubfield p t⟩ : frobeniusSubfield M p) =
      minpoly (↥(frobeniusSubfield M p)) t :=
    minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have hdeg : (minpoly (↥(frobeniusSubfield M p)) t).natDegree = p := by
    rw [← hmp, natDegree_X_pow_sub_C]
  have hli := linearIndependent_pow (K := ↥(frobeniusSubfield M p)) t
  rw [hdeg] at hli
  exact hli

end LinearIndependence

section AdjoinIndex

open scoped IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
  (p : ℕ) [hp : Fact p.Prime] [CharP K p]

private abbrev genT (t : M) : ↥K⟮t⟯ := IntermediateField.AdjoinSimple.gen K t

omit [CharP K p] in
private theorem genT_not_pow (t : M) (htr : Transcendental K t) (a : ↥K⟮t⟯) :
    a ^ p ≠ genT t := by
  intro ha
  have ht0 : t ≠ 0 := fun h ↦ htr (h ▸ isAlgebraic_zero)
  have ha' : t = (↑a : M) ^ p := by
    have := congrArg (fun z : ↥K⟮t⟯ ↦ (z : M)) ha
    push_cast at this; simpa using this.symm
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K _).mp a.2
  have hkey : aeval t (X * s ^ p - r ^ p) = 0 := by
    simp only [map_sub, map_mul, aeval_X, map_pow]
    rw [hrs, div_pow] at ha'
    by_cases hs0 : aeval t s = 0
    · rw [hs0, zero_pow hp.out.ne_zero, div_zero] at ha'
      exact absurd ha' ht0
    · rw [eq_div_iff (pow_ne_zero _ hs0)] at ha'
      rw [sub_eq_zero]; exact ha'
  have hinj : X * s ^ p - r ^ p = (0 : K[X]) := by
    have := htr
    rw [Transcendental, isAlgebraic_iff_not_injective, not_not] at this
    exact this (by simpa using hkey)
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hrs
    simp only [map_zero, div_zero] at hrs
    exact ht0 (ha'.trans (by rw [hrs, zero_pow hp.out.ne_zero]))
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.out.ne_zero, sub_zero, mul_eq_zero] at hinj
    exact hs0 (pow_eq_zero_iff hp.out.ne_zero |>.mp (hinj.resolve_left X_ne_zero))
  have hdeg : (X * s ^ p).natDegree = (r ^ p : K[X]).natDegree := by
    have := sub_eq_zero.mp hinj; rw [this]
  rw [natDegree_mul X_ne_zero (pow_ne_zero _ hs0), natDegree_X, natDegree_pow,
    natDegree_pow] at hdeg
  have hpdvd : p ∣ 1 := by
    have h1 : p * r.natDegree - p * s.natDegree = 1 := by omega
    exact ⟨r.natDegree - s.natDegree, by rw [Nat.mul_sub, h1]⟩
  exact absurd (Nat.le_of_dvd Nat.one_pos hpdvd) hp.out.one_lt.not_ge

private theorem adjoin_genT_over_frobeniusSubfield [PerfectField K] (t : M) :
    haveI : ExpChar (↥K⟮t⟯) p :=
      expChar_of_injective_algebraMap (algebraMap K _).injective p
    (IntermediateField.adjoin (↥(frobeniusSubfield (↥K⟮t⟯) p)) {genT t} :
        IntermediateField _ (↥K⟮t⟯)) = ⊤ := by
  haveI : ExpChar (↥K⟮t⟯) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  rw [eq_top_iff]
  intro x _

  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K _).mp x.2
  have hrs' : x = aeval (genT t) r / aeval (genT t) s := by
    apply Subtype.ext
    rw [hrs]
    push_cast
    exact congrArg₂ _
      (IntermediateField.AdjoinSimple.coe_aeval_gen_apply (F := K) (α := t) r).symm
      (IntermediateField.AdjoinSimple.coe_aeval_gen_apply (F := K) (α := t) s).symm
  rw [hrs']

  have hK : ∀ c : K, (algebraMap K (↥K⟮t⟯)) c ∈ (frobeniusSubfield (↥K⟮t⟯) p : Subfield _) := by
    intro c
    obtain ⟨c', hc'⟩ := (frobeniusEquiv K p).surjective c
    exact ⟨algebraMap K _ c', by
      rw [← hc']; simp only [frobenius_def, map_pow, frobeniusEquiv_apply, frobenius_def]⟩
  have haeval : ∀ q : K[X], aeval (genT t) q ∈
      (IntermediateField.adjoin (↥(frobeniusSubfield (↥K⟮t⟯) p)) {genT t} :
        IntermediateField _ (↥K⟮t⟯)) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c =>
      simp only [aeval_C]
      exact IntermediateField.algebraMap_mem _ (⟨_, hK c⟩ : ↥(frobeniusSubfield (↥K⟮t⟯) p))
    | add f g hf hg => simpa only [map_add] using add_mem hf hg
    | monomial n c _ =>
      simp only [map_mul, aeval_C, map_pow, aeval_X]
      exact mul_mem (IntermediateField.algebraMap_mem _
          (⟨_, hK c⟩ : ↥(frobeniusSubfield (↥K⟮t⟯) p)))
        (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _)
  exact div_mem (haeval r) (haeval s)

private theorem finrank_frobeniusSubfield_adjoin_transcendental [PerfectField K]
    {t : M} (htr : Transcendental K t) :
    haveI : ExpChar (↥(IntermediateField.adjoin K ({t} : Set M))) p :=
      expChar_of_injective_algebraMap (algebraMap K _).injective p
    Module.finrank
      (frobeniusSubfield (↥(IntermediateField.adjoin K ({t} : Set M))) p)
      (↥(IntermediateField.adjoin K ({t} : Set M))) = p := by
  haveI : ExpChar (↥K⟮t⟯) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  haveI : CharP (↥K⟮t⟯) p :=
    charP_of_injective_algebraMap (algebraMap K _).injective p

  let t' : ↥K⟮t⟯ := genT t
  let tp : ↥(frobeniusSubfield (↥K⟮t⟯) p) := ⟨t' ^ p, pow_mem_frobeniusSubfield p t'⟩
  have hint : IsIntegral (↥(frobeniusSubfield (↥K⟮t⟯) p)) t' := by
    refine ⟨X ^ p - C tp, monic_X_pow_sub_C _ hp.out.ne_zero, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C]
    exact sub_eq_zero.mpr rfl
  haveI hfd : FiniteDimensional (↥(frobeniusSubfield (↥K⟮t⟯) p)) (↥K⟮t⟯) := by
    have h1 := adjoin_genT_over_frobeniusSubfield (K := K) (M := M) p t
    have h2 := IntermediateField.adjoin.finiteDimensional hint
    rw [show t' = genT t from rfl, h1] at h2
    exact (IntermediateField.topEquiv (F := ↥(frobeniusSubfield (↥K⟮t⟯) p))
      (E := ↥K⟮t⟯)).toLinearEquiv.finiteDimensional

  have hli := pDigits_linearIndependent (M := ↥K⟮t⟯) p (t := t') (genT_not_pow p t htr)

  refine le_antisymm ?_
    (by simpa only [Fintype.card_fin] using hli.fintype_card_le_finrank)

  have htop := adjoin_genT_over_frobeniusSubfield (K := K) (M := M) p t
  calc Module.finrank _ (↥K⟮t⟯)
      = Module.finrank (↥(frobeniusSubfield (↥K⟮t⟯) p))
          (↥(IntermediateField.adjoin (↥(frobeniusSubfield (↥K⟮t⟯) p)) {t'} :
            IntermediateField _ (↥K⟮t⟯))) := by
        rw [show t' = genT t from rfl, htop, IntermediateField.finrank_top']
    _ = (minpoly (↥(frobeniusSubfield (↥K⟮t⟯) p)) t').natDegree :=
        IntermediateField.adjoin.finrank hint
    _ ≤ (X ^ p - C tp).natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ (by
          simp only [map_sub, map_pow, aeval_X, aeval_C]; exact sub_eq_zero.mpr rfl))
          (monic_X_pow_sub_C _ hp.out.ne_zero).ne_zero
    _ = p := natDegree_X_pow_sub_C _

end AdjoinIndex

/-- A one-variable function field over a perfect characteristic-`p` field has
degree `p` over its Frobenius subfield: if `t` is transcendental over `K` and
`M` is finite-dimensional over `K(t)`, then `[M : M^p] = p`. -/
public theorem finrank_frobeniusSubfield_eq_of_transcendental {K M : Type*} [Field K] [Field M]
    [Algebra K M] [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] :
    haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
    Module.finrank ↥(frobenius M p).fieldRange M = p := by
  haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
  show Module.finrank (frobeniusSubfield M p) M = p
  haveI : ExpChar (↥(IntermediateField.adjoin K ({t} : Set M))) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  haveI : FiniteDimensional
      (frobeniusSubfield (↥(IntermediateField.adjoin K ({t} : Set M))) p)
      (↥(IntermediateField.adjoin K ({t} : Set M))) :=
    FiniteDimensional.of_finrank_pos (by
      rw [finrank_frobeniusSubfield_adjoin_transcendental p htr]; exact hp.out.pos)
  rw [finrank_frobeniusSubfield_eq (E := ↥(IntermediateField.adjoin K ({t} : Set M))) p,
    finrank_frobeniusSubfield_adjoin_transcendental p htr]

end
