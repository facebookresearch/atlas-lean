/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing.lean`
and
`P2M/Sol/S_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing.lean`
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

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import MathlibExt.RingTheory.Henselian.EtaleLift

@[expose] public section

open Polynomial

namespace HenselIdem

universe u

section poly

variable {T : Type*} [CommRing T]

private noncomputable def poly {n : ℕ} (c : Fin n → T) : T[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

private theorem coeff_poly {n : ℕ} (c : Fin n → T) (j : ℕ) :
    (poly c).coeff j = if h : j < n then c ⟨j, h⟩ else 0 := by
  classical
  unfold poly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hj
      apply hb
      ext
      exact hj.symm
    · intro hj; exact absurd (Finset.mem_univ _) hj
  · apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro hj
    exact h (hj ▸ i.2)

private theorem coeff_poly_fin {n : ℕ} (c : Fin n → T) (i : Fin n) : (poly c).coeff i = c i := by
  rw [coeff_poly, dif_pos i.2]

private theorem degree_poly_lt {n : ℕ} (c : Fin n → T) : (poly c).degree < n :=
  degree_sum_fin_lt c

private theorem poly_coeff_eq_of_degree_lt {n : ℕ} (p : T[X]) (hp : p.degree < n) :
    poly (fun i : Fin n => p.coeff i) = p := by
  ext j
  rw [coeff_poly]
  split_ifs with h
  · rfl
  · symm
    apply coeff_eq_zero_of_degree_lt
    exact lt_of_lt_of_le hp (by exact_mod_cast not_lt.mp h)

private theorem poly_map {n : ℕ} (c : Fin n → T) {T' : Type*} [CommRing T'] (φ : T →+* T') :
    (poly c).map φ = poly (fun i => φ (c i)) := by
  unfold poly
  simp [Polynomial.map_sum]

private theorem poly_injective {n : ℕ} {c c' : Fin n → T} (h : poly c = poly c') : c = c' := by
  funext i
  rw [← coeff_poly_fin c i, ← coeff_poly_fin c' i, h]

private theorem eq_of_dvd_sub_of_degree_lt {F p q : T[X]} (hF : F.Monic)
    (hp : p.degree < F.degree) (hq : q.degree < F.degree) (h : F ∣ p - q) : p = q := by
  nontriviality T
  have h1 : (p - q) %ₘ F = 0 := (modByMonic_eq_zero_iff_dvd hF).mpr h
  have h2 : (p - q) %ₘ F = p - q :=
    (modByMonic_eq_self_iff hF).mpr (lt_of_le_of_lt (degree_sub_le p q) (max_lt hp hq))
  rw [h2] at h1
  exact sub_eq_zero.mp h1

end poly

section reduction

variable {B : Type*} [CommRing B] (J : Ideal B) (F : B[X]) (G : (B ⧸ J)[X])
  (hG : F.map (Ideal.Quotient.mk J) = G)

private noncomputable def redQuot : AdjoinRoot F →+* AdjoinRoot G :=
  AdjoinRoot.lift ((AdjoinRoot.of G).comp (Ideal.Quotient.mk J)) (AdjoinRoot.root G) (by
    rw [← Polynomial.eval₂_map, hG]
    exact AdjoinRoot.eval₂_root G)

include hG in
private theorem redQuot_mk (p : B[X]) :
    redQuot J F G hG (AdjoinRoot.mk F p) = AdjoinRoot.mk G (p.map (Ideal.Quotient.mk J)) := by
  unfold redQuot
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
    ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

private theorem redQuot_surjective : Function.Surjective (redQuot J F G hG) := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  exact ⟨AdjoinRoot.mk F q, redQuot_mk J F G hG q⟩

private theorem ker_redQuot_le :
    RingHom.ker (redQuot J F G hG) ≤ J.map (AdjoinRoot.of F) := by
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [RingHom.mem_ker, redQuot_mk, AdjoinRoot.mk_eq_zero] at hx
  obtain ⟨s, hs⟩ := hx
  obtain ⟨t, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective s
  have hmem : p - F * t ∈ (J.map (C : B →+* B[X])) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_sub,
      Polynomial.map_mul, hs, hG, sub_self, coeff_zero]
  have hp : AdjoinRoot.mk F p = AdjoinRoot.mk F (p - F * t) := by
    rw [AdjoinRoot.mk_eq_mk]
    exact ⟨t, by ring⟩
  rw [hp]
  have : (J.map (C : B →+* B[X])).map (AdjoinRoot.mk F) = J.map (AdjoinRoot.of F) := by
    rw [Ideal.map_map]
    rfl
  rw [← this]
  exact Ideal.mem_map_of_mem _ hmem

private theorem isNilpotent_of_mem_ker_redQuot (hJ : J ^ 2 = ⊥) {x : AdjoinRoot F}
    (hx : x ∈ RingHom.ker (redQuot J F G hG)) : IsNilpotent x := by
  refine ⟨2, ?_⟩
  have h1 : x ∈ J.map (AdjoinRoot.of F) := ker_redQuot_le J F G hG hx
  have h2 : x ^ 2 ∈ (J.map (AdjoinRoot.of F)) ^ 2 := Ideal.pow_mem_pow h1 2
  rw [← Ideal.map_pow, hJ, Ideal.map_bot] at h2
  exact (Ideal.mem_bot).mp h2

end reduction

section scheme

variable {R : Type u} [CommRing R] (f : R[X])

private abbrev P : Type u := MvPolynomial (Fin f.natDegree) R

private noncomputable def genericElem : (P f)[X] :=
  poly (fun i : Fin f.natDegree => (MvPolynomial.X i : P f))

private noncomputable def idemRem : (P f)[X] :=
  (genericElem f * genericElem f - genericElem f) %ₘ (f.map (algebraMap R (P f)))

private noncomputable def idemIdeal : Ideal (P f) := Ideal.span (↑(idemRem f).coeffs : Set (P f))

private theorem idemIdeal_fg : (idemIdeal f).FG := ⟨(idemRem f).coeffs, rfl⟩

private abbrev E : Type u := P f ⧸ idemIdeal f

variable {f}

section points

variable {B : Type*} [CommRing B] [Algebra R B]

private noncomputable def elemOf (ψ : P f →ₐ[R] B) : B[X] :=
  poly (fun i : Fin f.natDegree => ψ (MvPolynomial.X i))

private theorem genericElem_map (ψ : P f →ₐ[R] B) :
    (genericElem f).map (ψ : P f →+* B) = elemOf ψ := by
  unfold genericElem elemOf
  rw [poly_map]
  rfl

private theorem map_algebraMap_map (ψ : P f →ₐ[R] B) :
    (f.map (algebraMap R (P f))).map (ψ : P f →+* B) = f.map (algebraMap R B) := by
  rw [Polynomial.map_map, AlgHom.comp_algebraMap]

private theorem idemRem_map (hf : f.Monic) (ψ : P f →ₐ[R] B) :
    (idemRem f).map (ψ : P f →+* B) =
      (elemOf ψ * elemOf ψ - elemOf ψ) %ₘ (f.map (algebraMap R B)) := by
  unfold idemRem
  rw [map_modByMonic _ (hf.map _), Polynomial.map_sub, Polynomial.map_mul, genericElem_map,
    map_algebraMap_map]

private theorem forall_idemIdeal_iff (hf : f.Monic) (ψ : P f →ₐ[R] B) :
    (∀ a ∈ idemIdeal f, ψ a = 0) ↔
      IsIdempotentElem (AdjoinRoot.mk (f.map (algebraMap R B)) (elemOf ψ)) := by
  have key : (∀ a ∈ idemIdeal f, ψ a = 0) ↔ (idemRem f).map (ψ : P f →+* B) = 0 := by
    constructor
    · intro h
      ext j
      rw [coeff_map, coeff_zero]
      by_cases hj : (idemRem f).coeff j = 0
      · rw [hj]; exact map_zero _
      · exact h _ (Ideal.subset_span (Polynomial.coeff_mem_coeffs hj))
    · intro h a ha
      unfold idemIdeal at ha
      refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
      · intro x hx
        obtain ⟨j, -, rfl⟩ := (Polynomial.mem_coeffs_iff).mp hx
        have := congrArg (fun q => q.coeff j) h
        simpa [coeff_map] using this
      · exact map_zero _
      · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
      · intro r x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  rw [key, idemRem_map hf, modByMonic_eq_zero_iff_dvd (hf.map _), IsIdempotentElem,
    ← map_mul, AdjoinRoot.mk_eq_mk]

private theorem elemOf_comp {B' : Type*} [CommRing B'] [Algebra R B'] (χ : B →ₐ[R] B')
    (ψ : P f →ₐ[R] B) :
    elemOf (χ.comp ψ) = (elemOf ψ).map (χ : B →+* B') := by
  unfold elemOf
  rw [poly_map]
  rfl

private theorem degree_elemOf_lt (ψ : P f →ₐ[R] B) : (elemOf ψ).degree < f.natDegree :=
  degree_poly_lt _

private theorem degree_map_eq (hf : f.Monic) [Nontrivial B] :
    (f.map (algebraMap R B)).degree = f.natDegree := by
  rw [degree_eq_natDegree (hf.map _).ne_zero, hf.natDegree_map]

private theorem apply_X_eq_of_mk_eq (hf : f.Monic) {ψ₁ ψ₂ : P f →ₐ[R] B}
    (h : AdjoinRoot.mk (f.map (algebraMap R B)) (elemOf ψ₁) =
      AdjoinRoot.mk (f.map (algebraMap R B)) (elemOf ψ₂)) (i : Fin f.natDegree) :
    ψ₁ (MvPolynomial.X i) = ψ₂ (MvPolynomial.X i) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Subsingleton.elim _ _
  rw [AdjoinRoot.mk_eq_mk] at h
  have hdeg := degree_map_eq (B := B) hf
  have heq : elemOf ψ₁ = elemOf ψ₂ :=
    eq_of_dvd_sub_of_degree_lt (hf.map _) (hdeg ▸ degree_elemOf_lt ψ₁)
      (hdeg ▸ degree_elemOf_lt ψ₂) h
  exact congrFun (poly_injective heq) i

private noncomputable def evalAt (c : Fin f.natDegree → B) : P f →ₐ[R] B := MvPolynomial.aeval c

private theorem evalAt_X (c : Fin f.natDegree → B) (i : Fin f.natDegree) :
    evalAt (f := f) c (MvPolynomial.X i) = c i :=
  MvPolynomial.aeval_X c i

private theorem elemOf_evalAt (c : Fin f.natDegree → B) : elemOf (evalAt (f := f) c) = poly c := by
  unfold elemOf
  congr 1
  funext i
  exact evalAt_X c i

private theorem forall_idemIdeal_comp_mk (ψ : E f →ₐ[R] B) :
    ∀ a ∈ idemIdeal f, (ψ.comp (Ideal.Quotient.mkₐ R (idemIdeal f))) a = 0 := by
  intro a ha
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

private theorem exists_algHom_of_isIdempotentElem (hf : f.Monic)
    (x : AdjoinRoot (f.map (algebraMap R B))) (hx : IsIdempotentElem x) :
    ∃ ψ : E f →ₐ[R] B, AdjoinRoot.mk (f.map (algebraMap R B))
      (elemOf (ψ.comp (Ideal.Quotient.mkₐ R (idemIdeal f)))) = x := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Subsingleton (AdjoinRoot (f.map (algebraMap R B))) :=
      (AdjoinRoot.mk_surjective).subsingleton
    refine ⟨Ideal.Quotient.liftₐ (idemIdeal f) (evalAt (f := f) fun _ => 0) ?_,
      Subsingleton.elim _ _⟩
    intro a _; exact Subsingleton.elim _ _

  set y : B[X] := AdjoinRoot.modByMonicHom (hf.map (algebraMap R B)) x with hy
  have hyx : AdjoinRoot.mk (f.map (algebraMap R B)) y = x := AdjoinRoot.mk_leftInverse (hf.map _) x
  have hydeg : y.degree < f.natDegree := by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [hy, AdjoinRoot.modByMonicHom_mk, ← degree_map_eq (B := B) hf]
    exact degree_modByMonic_lt _ (hf.map _)
  set c : Fin f.natDegree → B := fun i => y.coeff i with hc
  have hpoly : poly c = y := poly_coeff_eq_of_degree_lt y hydeg
  have hkill : ∀ a ∈ idemIdeal f, evalAt (f := f) c a = 0 := by
    rw [forall_idemIdeal_iff hf, elemOf_evalAt, hpoly, hyx]
    exact hx
  refine ⟨Ideal.Quotient.liftₐ (idemIdeal f) (evalAt (f := f) c) hkill, ?_⟩
  have : (Ideal.Quotient.liftₐ (idemIdeal f) (evalAt (f := f) c) hkill).comp
      (Ideal.Quotient.mkₐ R (idemIdeal f)) = evalAt (f := f) c :=
    Ideal.Quotient.liftₐ_comp _ _ _
  rw [this, elemOf_evalAt, hpoly, hyx]

end points

private theorem formallyEtale_E (hf : f.Monic) : Algebra.FormallyEtale R (E f) := by
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ J hJ
  have hFG : (f.map (algebraMap R B)).map (Ideal.Quotient.mk J) = f.map (algebraMap R (B ⧸ J)) := by
    rw [Polynomial.map_map]
    rfl
  have hred : ∀ χ : P f →ₐ[R] B,
      redQuot J _ _ hFG (AdjoinRoot.mk _ (elemOf χ)) =
        AdjoinRoot.mk _ (elemOf ((Ideal.Quotient.mkₐ R J).comp χ)) := by
    intro χ
    rw [redQuot_mk, elemOf_comp]
    rfl
  constructor
  · intro ψ₁ ψ₂ h
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    have hi₁ := (forall_idemIdeal_iff hf _).mp (forall_idemIdeal_comp_mk ψ₁)
    have hi₂ := (forall_idemIdeal_iff hf _).mp (forall_idemIdeal_comp_mk ψ₂)
    have hcomp : (Ideal.Quotient.mkₐ R J).comp (ψ₁.comp (Ideal.Quotient.mkₐ R (idemIdeal f))) =
        (Ideal.Quotient.mkₐ R J).comp (ψ₂.comp (Ideal.Quotient.mkₐ R (idemIdeal f))) := by
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      exact congrArg (fun g => AlgHom.comp g (Ideal.Quotient.mkₐ R (idemIdeal f))) h
    have hnil : IsNilpotent
        (AdjoinRoot.mk (f.map (algebraMap R B))
            (elemOf (ψ₁.comp (Ideal.Quotient.mkₐ R (idemIdeal f)))) -
          AdjoinRoot.mk (f.map (algebraMap R B))
            (elemOf (ψ₂.comp (Ideal.Quotient.mkₐ R (idemIdeal f))))) := by
      apply isNilpotent_of_mem_ker_redQuot J _ _ hFG hJ
      rw [RingHom.mem_ker, map_sub, hred, hred, hcomp, sub_self]
    have heq := eq_of_isNilpotent_sub_of_isIdempotentElem hi₁ hi₂ hnil
    exact apply_X_eq_of_mk_eq hf heq i
  · intro g
    have hi := (forall_idemIdeal_iff hf _).mp (forall_idemIdeal_comp_mk g)
    obtain ⟨x, hx, hxred⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (redQuot J _ _ hFG)
      (fun x hx => isNilpotent_of_mem_ker_redQuot J _ _ hFG hJ hx) _
      (RingHom.mem_range.mpr (redQuot_surjective J _ _ hFG _)) hi
    obtain ⟨ψ, hψ⟩ := exists_algHom_of_isIdempotentElem hf x hx
    refine ⟨ψ, ?_⟩
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    have key : AdjoinRoot.mk (f.map (algebraMap R (B ⧸ J)))
        (elemOf (((Ideal.Quotient.mkₐ R J).comp ψ).comp (Ideal.Quotient.mkₐ R (idemIdeal f)))) =
        AdjoinRoot.mk (f.map (algebraMap R (B ⧸ J)))
          (elemOf (g.comp (Ideal.Quotient.mkₐ R (idemIdeal f)))) := by
      rw [← hxred, ← hψ, hred, AlgHom.comp_assoc]
    exact apply_X_eq_of_mk_eq hf key i

private theorem etale_E (hf : f.Monic) : Algebra.Etale R (E f) :=
  { formallyEtale := formallyEtale_E hf
    finitePresentation := Algebra.FinitePresentation.quotient (idemIdeal_fg f) }

end scheme

section hensel

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

open IsLocalRing

private theorem exists_dvd_and_map_residue_eq {f : R[X]} (hf : f.Monic)
    (e₀ : (ResidueField R)[X]) (hdeg : e₀.degree < f.natDegree)
    (he₀ : f.map (residue R) ∣ e₀ * e₀ - e₀) :
    ∃ e : R[X], e.degree < f.natDegree ∧ f ∣ e * e - e ∧ e.map (residue R) = e₀ := by

  set c₀ : Fin f.natDegree → ResidueField R := fun i => e₀.coeff i with hc₀
  have hpoly : poly c₀ = e₀ := poly_coeff_eq_of_degree_lt e₀ hdeg
  have hres : algebraMap R (ResidueField R) = residue R := rfl
  have hkill : ∀ a ∈ idemIdeal f, evalAt (f := f) c₀ a = 0 := by
    rw [forall_idemIdeal_iff hf, elemOf_evalAt, hpoly, IsIdempotentElem, ← map_mul,
      AdjoinRoot.mk_eq_mk, hres]
    exact he₀
  set φ : E f →ₐ[R] ResidueField R := Ideal.Quotient.liftₐ (idemIdeal f) (evalAt (f := f) c₀) hkill
    with hφ
  haveI : Algebra.Etale R (E f) := etale_E hf
  obtain ⟨ψ, hψ⟩ := HenselianLocalRing.exists_algHom_lift_of_etale (E f) φ
  set χ : P f →ₐ[R] R := ψ.comp (Ideal.Quotient.mkₐ R (idemIdeal f)) with hχ
  refine ⟨elemOf χ, degree_elemOf_lt χ, ?_, ?_⟩
  · have hi := (forall_idemIdeal_iff hf χ).mp (forall_idemIdeal_comp_mk ψ)
    rw [IsIdempotentElem, ← map_mul, AdjoinRoot.mk_eq_mk, Algebra.algebraMap_self,
      Polynomial.map_id] at hi
    exact hi
  · have h1 : (elemOf χ).map (residue R) = elemOf ((Algebra.ofId R (ResidueField R)).comp χ) := by
      rw [elemOf_comp (Algebra.ofId R (ResidueField R)) χ]
      rfl
    have h2 : (Algebra.ofId R (ResidueField R)).comp χ = evalAt (f := f) c₀ := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [hχ, AlgHom.comp_apply, AlgHom.comp_apply, Algebra.ofId_apply, hψ, hφ,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply]
      change (evalAt (f := f) c₀) (MvPolynomial.X i) = (evalAt (f := f) c₀) (MvPolynomial.X i)
      rfl
    rw [h1, h2, elemOf_evalAt, hpoly]

end hensel

section finite

open IsLocalRing

variable {R : Type u} [CommRing R]

private theorem exists_isIdempotentElem_of_isArtinianRing {C : Type*} [CommRing C]
    [IsArtinianRing C] (c : C) : ∃ (N : ℕ) (d : C), 1 ≤ N ∧ IsIdempotentElem (d * c ^ N) ∧
      c ^ N = (d * c ^ N) * c ^ N := by
  let g : ℕ →o (Ideal C)ᵒᵈ :=
    ⟨fun k => OrderDual.toDual (Ideal.span {c ^ k}), fun k m hkm =>
      OrderDual.toDual_le_toDual.mpr
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow c hkm))⟩
  obtain ⟨N₀, hN₀⟩ := IsArtinian.monotone_stabilizes g
  set N := N₀ + 1 with hN
  have hst : Ideal.span {c ^ N} = Ideal.span {c ^ (2 * N)} := by
    have h1 := hN₀ N (by omega)
    have h2 := hN₀ (2 * N) (by omega)
    have : g N = g (2 * N) := h1.symm.trans h2
    exact OrderDual.toDual.injective this
  have hmem : c ^ N ∈ Ideal.span {c ^ (2 * N)} := hst ▸ Ideal.mem_span_singleton_self _
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨N, d, by omega, ?_, ?_⟩
  · unfold IsIdempotentElem
    calc d * c ^ N * (d * c ^ N) = d * (d * c ^ (2 * N)) := by ring
      _ = d * c ^ N := by rw [hd]
  · calc c ^ N = d * c ^ (2 * N) := hd.symm
      _ = d * c ^ N * c ^ N := by ring

private theorem map_maximalIdeal_le_jacobson [IsLocalRing R] {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] :
    (maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro 𝔫 ⟨-, h𝔫⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (𝔫.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) 𝔫
  rw [IsLocalRing.eq_maximalIdeal this]

private theorem eq_of_sub_mem_jacobson {S : Type*} [CommRing S] {e₁ e₂ : S}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
    (h : e₁ - e₂ ∈ Ideal.jacobson (⊥ : Ideal S)) :
    e₁ = e₂ := by
  have h3 : (e₁ - e₂) ^ 3 = e₁ - e₂ := by
    have h1 := he₁.eq
    have h2 := he₂.eq
    have : (e₁ - e₂) ^ 3 =
        e₁ * e₁ * e₁ - 3 * (e₁ * e₁) * e₂ + 3 * e₁ * (e₂ * e₂) - e₂ * e₂ * e₂ := by ring
    rw [this, h1, h1, h2, h2]
    ring
  have hsq : (e₁ - e₂) ^ 2 ∈ Ideal.jacobson (⊥ : Ideal S) :=
    Ideal.pow_mem_of_mem _ h 2 (by norm_num)
  have hu : IsUnit ((e₁ - e₂) ^ 2 * (-1) + 1) := Ideal.mem_jacobson_bot.mp hsq (-1)
  have hzero : (e₁ - e₂) * ((e₁ - e₂) ^ 2 * (-1) + 1) = 0 := by
    have : (e₁ - e₂) * ((e₁ - e₂) ^ 2 * (-1) + 1) = (e₁ - e₂) - (e₁ - e₂) ^ 3 := by ring
    rw [this, h3, sub_self]
  have := (IsUnit.mul_left_eq_zero hu).mp hzero
  exact sub_eq_zero.mp this

variable [HenselianLocalRing R]

private theorem existsUnique_isIdempotentElem_mk_eq {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (ē : S ⧸ (maximalIdeal R).map (algebraMap R S)) (hē : IsIdempotentElem ē) :
    ∃! e : S, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) e = ē := by

  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective ē
  set 𝔪S := (maximalIdeal R).map (algebraMap R S) with h𝔪S
  obtain ⟨f, hf, hfs⟩ : IsIntegral R s := Algebra.IsIntegral.isIntegral s

  set κ := ResidueField R
  set j : κ →+* S ⧸ 𝔪S := Ideal.Quotient.lift (maximalIdeal R)
    ((Ideal.Quotient.mk 𝔪S).comp (algebraMap R S)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha) with hj
  have hjres : j.comp (residue R) = (Ideal.Quotient.mk 𝔪S).comp (algebraMap R S) := by
    ext a; rfl

  set fκ : κ[X] := f.map (residue R) with hfκ
  have hfκm : fκ.Monic := hf.map _
  have hπ0 : fκ.eval₂ j (Ideal.Quotient.mk 𝔪S s) = 0 := by
    rw [hfκ, Polynomial.eval₂_map, hjres, ← Polynomial.hom_eval₂, hfs, map_zero]
  set π : AdjoinRoot fκ →+* S ⧸ 𝔪S := AdjoinRoot.lift j (Ideal.Quotient.mk 𝔪S s) hπ0 with hπ
  have hπroot : π (AdjoinRoot.root fκ) = Ideal.Quotient.mk 𝔪S s := by
    rw [hπ, AdjoinRoot.lift_root]
  have hπmk : ∀ p : R[X], π (AdjoinRoot.mk fκ (p.map (residue R))) =
      Ideal.Quotient.mk 𝔪S (p.eval₂ (algebraMap R S) s) := by
    intro p
    rw [hπ, AdjoinRoot.lift_mk, Polynomial.eval₂_map, hjres, ← Polynomial.hom_eval₂]

  haveI : Module.Finite κ (AdjoinRoot fκ) := hfκm.finite_adjoinRoot
  haveI : IsArtinianRing (AdjoinRoot fκ) := IsArtinianRing.of_finite κ (AdjoinRoot fκ)
  obtain ⟨N, d, hN1, hε, hcN⟩ := exists_isIdempotentElem_of_isArtinianRing (AdjoinRoot.root fκ)
  set ε := d * AdjoinRoot.root fκ ^ N with hεdef

  have hb : IsIdempotentElem (Ideal.Quotient.mk 𝔪S s) := hē
  have hπcN : π (AdjoinRoot.root fκ ^ N) = Ideal.Quotient.mk 𝔪S s := by
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    rw [map_pow, hπroot, hb.pow_succ_eq]
  have hπε : π ε = Ideal.Quotient.mk 𝔪S s := by
    have ha : π ε * Ideal.Quotient.mk 𝔪S s = π ε := by
      rw [hεdef, map_mul, hπcN, mul_assoc, hb.eq]
    have hb' : Ideal.Quotient.mk 𝔪S s = π ε * Ideal.Quotient.mk 𝔪S s := by
      conv_lhs => rw [← hπcN, hcN, map_mul, hπcN]
    rw [← ha, ← hb']

  rcases subsingleton_or_nontrivial κ with hκ | hκ
  · haveI : Subsingleton (S ⧸ 𝔪S) := by
      have h1 : (1 : S ⧸ 𝔪S) = 0 := by
        rw [← map_one j, Subsingleton.elim (1 : κ) 0, map_zero]
      exact subsingleton_of_zero_eq_one h1.symm
    refine ⟨0, ⟨IsIdempotentElem.zero, Subsingleton.elim _ _⟩, ?_⟩
    rintro e ⟨he, -⟩
    apply eq_of_sub_mem_jacobson he IsIdempotentElem.zero
    apply map_maximalIdeal_le_jacobson (R := R)
    rw [sub_zero, ← Ideal.Quotient.eq_zero_iff_mem]
    exact Subsingleton.elim _ _
  set e₀ : κ[X] := AdjoinRoot.modByMonicHom hfκm ε with he₀
  have he₀ε : AdjoinRoot.mk fκ e₀ = ε := AdjoinRoot.mk_leftInverse hfκm ε
  have hdeg : e₀.degree < f.natDegree := by
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective ε
    rw [he₀, ← hp, AdjoinRoot.modByMonicHom_mk, ← hf.natDegree_map (residue R),
      ← degree_eq_natDegree hfκm.ne_zero]
    exact degree_modByMonic_lt _ hfκm
  have hidem : fκ ∣ e₀ * e₀ - e₀ := by
    rw [← AdjoinRoot.mk_eq_mk, map_mul, he₀ε]
    exact hε
  obtain ⟨e, -, hediv, hemap⟩ := exists_dvd_and_map_residue_eq hf e₀ hdeg hidem

  refine ⟨e.eval₂ (algebraMap R S) s, ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨t, ht⟩ := hediv
    have := congrArg (fun p => p.eval₂ (algebraMap R S) s) ht
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, hfs, zero_mul] at this
    exact sub_eq_zero.mp this
  · rw [← hπmk, hemap, he₀ε, hπε]
  · rintro e' ⟨he', he'mk⟩
    have hidem' : IsIdempotentElem (e.eval₂ (algebraMap R S) s) := by
      obtain ⟨t, ht⟩ := hediv
      have := congrArg (fun p => p.eval₂ (algebraMap R S) s) ht
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, hfs, zero_mul] at this
      exact sub_eq_zero.mp this
    apply eq_of_sub_mem_jacobson he' hidem'
    apply map_maximalIdeal_le_jacobson (R := R)
    rw [← Ideal.Quotient.eq, he'mk, ← hπmk, hemap, he₀ε, hπε]

end finite

end HenselIdem

universe u v

namespace S17Hens

private theorem isArtinianRing_quotient_map_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  let k := R ⧸ IsLocalRing.maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  have hJR : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (S ⧸ J) r = 0 := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  letI : Algebra k (S ⧸ J) := (Ideal.Quotient.lift _ (algebraMap R (S ⧸ J)) hJR).toAlgebra
  haveI : IsScalarTower R k (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Module.Finite k (S ⧸ J) := Module.Finite.of_restrictScalars_finite R k (S ⧸ J)
  exact IsArtinianRing.of_finite k (S ⧸ J)

private theorem isLocalRing_of_isDomain_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hS

  have h1 : ∃ a : S, ¬ IsUnit a ∧ ¬ IsUnit (1 - a) := by
    by_contra h
    push Not at h
    exact hS (IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      by_cases ha : IsUnit a
      · exact Or.inl ha
      · exact Or.inr (h a ha))
  obtain ⟨a, ha, ha'⟩ := h1
  obtain ⟨m₁, hm₁, ham₁⟩ := exists_max_ideal_of_mem_nonunits ha
  obtain ⟨m₂, hm₂, ham₂⟩ := exists_max_ideal_of_mem_nonunits ha'
  have hne : m₁ ≠ m₂ := by
    intro h
    subst h
    have : (1 : S) ∈ m₁ := by
      have := m₁.add_mem ham₁ ham₂
      rwa [add_sub_cancel] at this
    exact hm₁.ne_top ((Ideal.eq_top_iff_one _).mpr this)

  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  have hJle : ∀ m : Ideal S, m.IsMaximal → J ≤ m := by
    intro m hm
    rw [hJ, Ideal.map_le_iff_le_comap]
    haveI := hm
    have hmax : (m.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m
    rw [IsLocalRing.eq_maximalIdeal hmax]

  haveI : IsArtinianRing (S ⧸ J) := isArtinianRing_quotient_map_maximalIdeal
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hmaxq : ∀ m : Ideal S, m.IsMaximal → (m.map (Ideal.Quotient.mk J)).IsMaximal := by
    intro m hm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm with h | h
    · exfalso
      have : m = ⊤ := by
        have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h
        rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top] at h2
        have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        rw [hker, sup_eq_left.mpr (hJle m hm)] at h2
        exact h2
      exact hm.ne_top this
    · exact h
  let M₁ : MaximalSpectrum (S ⧸ J) := ⟨m₁.map (Ideal.Quotient.mk J), hmaxq m₁ hm₁⟩
  let M₂ : MaximalSpectrum (S ⧸ J) := ⟨m₂.map (Ideal.Quotient.mk J), hmaxq m₂ hm₂⟩
  have hM : M₁ ≠ M₂ := by
    intro h
    apply hne
    have h2 : m₁.map (Ideal.Quotient.mk J) = m₂.map (Ideal.Quotient.mk J) :=
      congrArg MaximalSpectrum.asIdeal h
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h2
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_map_of_surjective _ hsurj] at h3
    have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [hker, sup_eq_left.mpr (hJle m₁ hm₁), sup_eq_left.mpr (hJle m₂ hm₂)] at h3

  let π := IsArtinianRing.quotNilradicalEquivPi (S ⧸ J)
  let f₀ : ∀ I : MaximalSpectrum (S ⧸ J), (S ⧸ J) ⧸ I.asIdeal := Pi.single M₁ 1
  have hf₀ : IsIdempotentElem f₀ := by
    show f₀ * f₀ = f₀
    ext I
    by_cases hI : I = M₁
    · subst hI; simp [f₀]
    · simp [f₀, hI]
  have hf₀0 : f₀ ≠ 0 := by
    intro h
    have := congrFun h M₁
    simp [f₀] at this
    exact M₁.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this.symm)
  have hf₀1 : f₀ ≠ 1 := by
    intro h
    have := congrFun h M₂
    have h0 : f₀ M₂ = 0 := Pi.single_eq_of_ne hM.symm _
    rw [h0, Pi.one_apply] at this
    exact M₂.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this)
  let ē₀ := π.symm f₀
  have hē₀ : IsIdempotentElem ē₀ := by
    show π.symm f₀ * π.symm f₀ = π.symm f₀
    rw [← map_mul, hf₀.eq]

  have hnil : ∀ y ∈ RingHom.ker (Ideal.Quotient.mk (nilradical (S ⧸ J))), IsNilpotent y := by
    intro y hy
    rw [Ideal.mk_ker] at hy
    exact hy
  obtain ⟨ē, hē, hēē₀⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk (nilradical (S ⧸ J))) hnil ē₀
    (Ideal.Quotient.mk_surjective ē₀) hē₀

  obtain ⟨e, ⟨he, hemk⟩, -⟩ := HenselIdem.existsUnique_isIdempotentElem_mk_eq ē hē

  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h0 | h1
  · apply hf₀0
    have : ē = 0 := by rw [← hemk, h0, map_zero]
    have : ē₀ = 0 := by rw [← hēē₀, this, map_zero]
    have : f₀ = π 0 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_zero]
  · apply hf₀1
    have : ē = 1 := by rw [← hemk, h1, map_one]
    have : ē₀ = 1 := by rw [← hēē₀, this, map_one]
    have : f₀ = π 1 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_one]

end S17Hens

namespace EsbG2bPrufer

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

private theorem val_le_one_of_isIntegral (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) {b : F} (hb : IsIntegral ↥O b) :
    O'.valuation b ≤ 1 := by
  obtain ⟨p, hpm, hpe⟩ := hb
  by_contra hgt
  rw [not_le] at hgt
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hgt
    exact absurd hgt (by simp)
  have hvb0 : O'.valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
  have hn : p.natDegree ≠ 0 := by
    intro h0
    have h1 : p = 1 := hpm.natDegree_eq_zero.mp h0
    rw [h1, Polynomial.eval₂_one] at hpe
    exact one_ne_zero hpe
  have hrel : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap ↥O F (p.coeff i) * b ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpe
  rw [Finset.sum_range_succ, Polynomial.Monic.coeff_natDegree hpm, map_one, one_mul] at hrel
  have hbn : b ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree, algebraMap ↥O F (p.coeff i) * b ^ i :=
    eq_neg_of_add_eq_zero_right hrel
  have hlt : O'.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap ↥O F (p.coeff i) * b ^ i) < O'.valuation b ^ p.natDegree := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ hvb0) fun i hi => ?_
    rw [map_mul, map_pow]
    calc O'.valuation (algebraMap ↥O F (p.coeff i)) * O'.valuation b ^ i
        ≤ 1 * O'.valuation b ^ i := by
          gcongr
          exact O'.valuation_le_one ⟨_, (hO _).mpr (p.coeff i).2⟩
      _ = O'.valuation b ^ i := one_mul _
      _ < O'.valuation b ^ p.natDegree := by
          exact pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi)
  rw [← map_pow, hbn, Valuation.map_neg] at hlt
  exact lt_irrefl _ hlt

private def tail (A : ℕ → E) (x : F) (n j : ℕ) : F :=
  ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ))

private theorem tail_top (A : ℕ → E) (x : F) (n : ℕ) : tail A x n (n + 1) = 0 := by
  rw [tail, Finset.Ico_self, Finset.sum_empty]

private theorem tail_pull (A : ℕ → E) {x : F} (hx0 : x ≠ 0) (n j : ℕ) :
    x ^ (j : ℤ) * tail A x n j
      = ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) := by
  rw [tail, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc x ^ (j : ℤ) * (algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)))
      = algebraMap E F (A i) * (x ^ (j : ℤ) * x ^ ((i : ℤ) - (j : ℤ))) := by ring
    _ = algebraMap E F (A i) * x ^ ((j : ℤ) + ((i : ℤ) - (j : ℤ))) := by
        rw [zpow_add₀ hx0]
    _ = algebraMap E F (A i) * x ^ (i : ℤ) := by
        rw [show (j : ℤ) + ((i : ℤ) - (j : ℤ)) = (i : ℤ) from by omega]

private theorem tail_eq_neg (A : ℕ → E) {x : F} (hx0 : x ≠ 0) {n : ℕ}
    (hrel : ∑ i ∈ Finset.range (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) = 0)
    {j : ℕ} (hj : j ≤ n + 1) :
    tail A x n j = -∑ i ∈ Finset.range j, algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)) := by
  have hxj : x ^ (j : ℤ) ≠ 0 := zpow_ne_zero _ hx0
  have hsplit : ∑ i ∈ Finset.range j, algebraMap E F (A i) * x ^ (i : ℤ)
      + ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) = 0 := by
    rw [Finset.range_eq_Ico] at hrel ⊢
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le j) hj]
    exact hrel
  have h1 : ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ)
      = -∑ i ∈ Finset.range j, algebraMap E F (A i) * x ^ (i : ℤ) :=
    eq_neg_of_add_eq_zero_right hsplit
  refine mul_left_cancel₀ hxj ?_
  rw [tail_pull A hx0 n j, h1, mul_neg, neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc algebraMap E F (A i) * x ^ (i : ℤ)
      = algebraMap E F (A i) * x ^ ((j : ℤ) + ((i : ℤ) - (j : ℤ))) := by
        rw [show (j : ℤ) + ((i : ℤ) - (j : ℤ)) = (i : ℤ) from by omega]
    _ = algebraMap E F (A i) * (x ^ (j : ℤ) * x ^ ((i : ℤ) - (j : ℤ))) := by
        rw [zpow_add₀ hx0]
    _ = x ^ (j : ℤ) * (algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ))) := by ring

private theorem tail_horner (A : ℕ → E) {x : F} (hx0 : x ≠ 0) {n : ℕ}
    {j : ℕ} (hj : j ≤ n) :
    tail A x n j = algebraMap E F (A j) + x * tail A x n (j + 1) := by
  have hxj : x ^ (j : ℤ) ≠ 0 := zpow_ne_zero _ hx0
  refine mul_left_cancel₀ hxj ?_
  have hpull := tail_pull A hx0 n j
  have hpull1 := tail_pull A hx0 n (j + 1)
  have hbot : ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ)
      = algebraMap E F (A j) * x ^ (j : ℤ)
        + ∑ i ∈ Finset.Ico (j + 1) (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) :=
    Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hj) _
  have hx1 : x ^ ((j : ℤ) + 1) = x ^ (j : ℤ) * x := by
    rw [zpow_add₀ hx0, zpow_one]
  calc x ^ (j : ℤ) * tail A x n j
      = algebraMap E F (A j) * x ^ (j : ℤ)
        + ∑ i ∈ Finset.Ico (j + 1) (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) := by
        rw [hpull, hbot]
    _ = algebraMap E F (A j) * x ^ (j : ℤ) + x ^ ((j + 1 : ℕ) : ℤ) * tail A x n (j + 1) := by
        rw [hpull1]
    _ = x ^ (j : ℤ) * (algebraMap E F (A j) + x * tail A x n (j + 1)) := by
        have h2 : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by omega
        rw [h2, hx1]
        ring

private theorem exists_rep [Algebra.IsAlgebraic E F] (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) {x : F} (hxO : x ∈ O') (hx0 : x ≠ 0) :
    ∃ b s : ↥(integralClosure ↥O F), O'.valuation (s : F) = 1 ∧ x * ↑s = ↑b := by
  classical
  obtain ⟨p, hp0, hpe⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) x
  set n := p.natDegree with hndef
  have hvx : O'.valuation x ≤ 1 := (O'.valuation_le_one_iff x).mpr hxO

  have hn0 : n ≠ 0 := by
    intro h0
    have hc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    rw [hc, Polynomial.aeval_C] at hpe
    have : p.coeff 0 = 0 := by
      have := (map_eq_zero (algebraMap E F)).mp hpe
      exact this
    rw [this, map_zero] at hc
    exact hp0 hc

  have hrel0 : ∑ i ∈ Finset.range (n + 1), algebraMap E F (p.coeff i) * x ^ (i : ℤ) = 0 := by
    have h1 := hpe
    rw [Polynomial.aeval_eq_sum_range] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, zpow_natCast]

  obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1))
      (fun i => O'.valuation (algebraMap E F (p.coeff i))) ⟨0, Finset.mem_range.mpr n.succ_pos⟩
  have hcn : p.coeff n ≠ 0 := by
    rw [hndef]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hvi₀pos : 0 < O'.valuation (algebraMap E F (p.coeff i₀)) := by
    have h1 : O'.valuation (algebraMap E F (p.coeff n))
        ≤ O'.valuation (algebraMap E F (p.coeff i₀)) :=
      hi₀max n (Finset.mem_range.mpr n.lt_succ_self)
    have h2 : O'.valuation (algebraMap E F (p.coeff n)) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact fun h => hcn ((map_eq_zero (algebraMap E F)).mp h)
    exact lt_of_lt_of_le (zero_lt_iff.mpr h2) h1
  have hci₀ : p.coeff i₀ ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hvi₀pos
    exact lt_irrefl 0 hvi₀pos

  set A : ℕ → E := fun i => p.coeff i / p.coeff i₀ with hAdef
  have hAi₀ : A i₀ = 1 := div_self hci₀
  have hvA : ∀ i, O'.valuation (algebraMap E F (A i))
      = O'.valuation (algebraMap E F (p.coeff i))
        / O'.valuation (algebraMap E F (p.coeff i₀)) := by
    intro i
    rw [hAdef]
    dsimp only
    rw [map_div₀, map_div₀]
  have hAle : ∀ i ∈ Finset.range (n + 1), O'.valuation (algebraMap E F (A i)) ≤ 1 := by
    intro i hi
    rw [hvA i, div_le_one₀ hvi₀pos]
    exact hi₀max i hi
  have hAmemO : ∀ i ∈ Finset.range (n + 1), A i ∈ O := fun i hi =>
    (hO _).mp (O'.mem_of_valuation_le_one _ (hAle i hi))

  have hrelA : ∑ i ∈ Finset.range (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) = 0 := by
    have h1 : ∀ i, algebraMap E F (A i) * x ^ (i : ℤ)
        = algebraMap E F (p.coeff i) * x ^ (i : ℤ) * (algebraMap E F (p.coeff i₀))⁻¹ := by
      intro i
      rw [hAdef]
      dsimp only
      rw [div_eq_mul_inv, map_mul, map_inv₀]
      ring
    calc ∑ i ∈ Finset.range (n + 1), algebraMap E F (A i) * x ^ (i : ℤ)
        = (∑ i ∈ Finset.range (n + 1), algebraMap E F (p.coeff i) * x ^ (i : ℤ))
          * (algebraMap E F (p.coeff i₀))⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => h1 i
      _ = 0 := by rw [hrel0, zero_mul]

  have hS : (Finset.filter (fun i => O'.valuation (algebraMap E F (A i)) = 1)
      (Finset.range (n + 1))).Nonempty := by
    refine ⟨i₀, Finset.mem_filter.mpr ⟨hi₀mem, ?_⟩⟩
    rw [hAi₀, map_one, map_one]
  set k := (Finset.filter (fun i => O'.valuation (algebraMap E F (A i)) = 1)
      (Finset.range (n + 1))).max' hS with hkdef
  have hkmem := (Finset.filter (fun i => O'.valuation (algebraMap E F (A i)) = 1)
      (Finset.range (n + 1))).max'_mem hS
  rw [← hkdef] at hkmem
  have hkrange : k ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hkmem).1
  have hvAk : O'.valuation (algebraMap E F (A k)) = 1 := (Finset.mem_filter.mp hkmem).2
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkrange)
  have hklt : ∀ i ∈ Finset.range (n + 1), k < i →
      O'.valuation (algebraMap E F (A i)) < 1 := by
    intro i hi hik
    refine lt_of_le_of_ne (hAle i hi) fun he => ?_
    have : i ≤ k := Finset.le_max' _ i (Finset.mem_filter.mpr ⟨hi, he⟩)
    omega

  set W : Submodule ↥O F :=
    Submodule.span ↥O (((Finset.range (2 * n + 1)).image
      fun m : ℕ => x ^ ((m : ℤ) - (n : ℤ))) : Finset F) with hWdef
  have hgen : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ (n : ℤ) → x ^ m ∈ W := by
    intro m h1 h2
    refine Submodule.subset_span ?_
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨(m + (n : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    rw [show (((m + (n : ℤ)).toNat : ℤ) - (n : ℤ)) = m from by omega]
  have hWfg : W.FG := Submodule.fg_span (Finset.finite_toSet _)
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h1 : (1 : F) ∈ W := by
      have := hgen 0 (by omega) (by omega)
      rwa [zpow_zero] at this
    rw [hbot, Submodule.mem_bot] at h1
    exact one_ne_zero h1

  have hsmul : ∀ (a : E) (ha : a ∈ O) (y : F),
      algebraMap E F a * y = (⟨a, ha⟩ : ↥O) • y := by
    intro a ha y
    rw [Algebra.smul_def]
    rfl

  have hTmemW : ∀ j ≤ n, tail A x n j ∈ W := by
    intro j hj
    rw [tail]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi' := Finset.mem_Ico.mp hi
    rw [hsmul (A i) (hAmemO i (Finset.mem_range.mpr hi'.2)) _]
    refine Submodule.smul_mem _ _ (hgen _ (by omega) (by omega))

  have hstab : ∀ j ≤ n, ∀ w ∈ W, tail A x n j * w ∈ W := by
    intro j hj w hw
    induction hw using Submodule.span_induction with
    | mem w hwmem =>
      rw [Finset.mem_coe, Finset.mem_image] at hwmem
      obtain ⟨m0, hm0r, rfl⟩ := hwmem
      have hm0' : m0 < 2 * n + 1 := Finset.mem_range.mp hm0r
      rcases le_or_gt 0 ((m0 : ℤ) - (n : ℤ)) with hmnn | hmnn
      · rw [tail_eq_neg A hx0 hrelA (le_trans hj (Nat.le_succ n)), neg_mul, Finset.sum_mul]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        have he : algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)) * x ^ ((m0 : ℤ) - (n : ℤ))
            = algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ) + ((m0 : ℤ) - (n : ℤ))) := by
          rw [mul_assoc, ← zpow_add₀ hx0]
        rw [he, hsmul (A i) (hAmemO i (Finset.mem_range.mpr (by omega))) _]
        refine Submodule.smul_mem _ _ (hgen _ (by omega) (by omega))
      · rw [tail, Finset.sum_mul]
        refine Submodule.sum_mem _ fun i hi => ?_
        have hi' := Finset.mem_Ico.mp hi
        have he : algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)) * x ^ ((m0 : ℤ) - (n : ℤ))
            = algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ) + ((m0 : ℤ) - (n : ℤ))) := by
          rw [mul_assoc, ← zpow_add₀ hx0]
        rw [he, hsmul (A i) (hAmemO i (Finset.mem_range.mpr hi'.2)) _]
        refine Submodule.smul_mem _ _ (hgen _ (by omega) (by omega))
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ ha

  have hTint : ∀ j ≤ n, IsIntegral ↥O (tail A x n j) := by
    intro j hj
    refine isIntegral_of_smul_mem_submodule W hWne hWfg _ fun w hw => ?_
    rw [smul_eq_mul]
    exact hstab j hj w hw

  have hTk1 : O'.valuation (tail A x n (k + 1)) < 1 := by
    rcases eq_or_lt_of_le hkn with heq | hklt'
    · rw [heq, tail_top, map_zero]
      exact zero_lt_one
    · rw [tail]
      refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      have hnn : (0 : ℤ) ≤ (i : ℤ) - ((k + 1 : ℕ) : ℤ) := by omega
      have hz : x ^ ((i : ℤ) - ((k + 1 : ℕ) : ℤ)) = x ^ (i - (k + 1)) := by
        rw [← zpow_natCast x (i - (k + 1))]
        congr 1
        omega
      rw [map_mul, hz, map_pow]
      calc O'.valuation (algebraMap E F (A i)) * O'.valuation x ^ (i - (k + 1))
          ≤ O'.valuation (algebraMap E F (A i)) * 1 := by
            gcongr
            exact pow_le_one₀ zero_le' hvx
        _ = O'.valuation (algebraMap E F (A i)) := mul_one _
        _ < 1 := hklt i (Finset.mem_range.mpr hi'.2) (by omega)

  have hvTk : O'.valuation (tail A x n k) = 1 := by
    have hh := tail_horner A hx0 hkn
    have hsmall : O'.valuation (x * tail A x n (k + 1)) < 1 := by
      rw [map_mul]
      calc O'.valuation x * O'.valuation (tail A x n (k + 1))
          ≤ 1 * O'.valuation (tail A x n (k + 1)) := by gcongr
        _ = O'.valuation (tail A x n (k + 1)) := one_mul _
        _ < 1 := hTk1
    have hne : O'.valuation (x * tail A x n (k + 1))
        < O'.valuation (algebraMap E F (A k)) := by
      rw [hvAk]
      exact hsmall
    rw [hh, Valuation.map_add_eq_of_lt_left _ hne]
    exact hvAk

  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk00 : k = 0 := by omega
    have hT0 : tail A x n 0 = 0 := by
      have h1 := tail_eq_neg A hx0 hrelA (Nat.zero_le (n + 1))
      rw [h1, Finset.range_zero, Finset.sum_empty, neg_zero]
    have hh := tail_horner A hx0 (Nat.zero_le n)
    rw [hT0] at hh
    have h2 : algebraMap E F (A 0) = -(x * tail A x n 1) :=
      eq_neg_of_add_eq_zero_left hh.symm
    have h3 : O'.valuation (algebraMap E F (A 0)) < 1 := by
      rw [h2, Valuation.map_neg, map_mul]
      have hk1' : O'.valuation (tail A x n 1) < 1 := by
        have := hTk1
        rwa [hk00, zero_add] at this
      calc O'.valuation x * O'.valuation (tail A x n 1)
          ≤ 1 * O'.valuation (tail A x n 1) := by gcongr
        _ = O'.valuation (tail A x n 1) := one_mul _
        _ < 1 := hk1'
    rw [hk00] at hvAk
    rw [hvAk] at h3
    exact lt_irrefl 1 h3

  have hkn1 : k - 1 ≤ n := by omega
  have hk1k : (k - 1) + 1 = k := by omega
  have hbint : IsIntegral ↥O (tail A x n (k - 1) - algebraMap E F (A (k - 1))) := by
    refine (hTint (k - 1) hkn1).sub ?_
    have hmem : A (k - 1) ∈ O := hAmemO (k - 1) (Finset.mem_range.mpr (by omega))
    exact isIntegral_algebraMap (x := (⟨A (k - 1), hmem⟩ : ↥O))
  have hmul : x * tail A x n k = tail A x n (k - 1) - algebraMap E F (A (k - 1)) := by
    have hh := tail_horner A hx0 hkn1
    rw [hk1k] at hh
    rw [hh]
    ring
  exact ⟨⟨_, hbint⟩, ⟨_, hTint k hkn⟩, hvTk, hmul⟩

private theorem mem_iff_rep [Algebra.IsAlgebraic E F] (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) (x : F) :
    x ∈ O' ↔ ∃ b s : ↥(integralClosure ↥O F), O'.valuation (s : F) = 1 ∧ x * ↑s = ↑b := by
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨0, 1, ?_, ?_⟩
      · rw [OneMemClass.coe_one, map_one]
      · rw [OneMemClass.coe_one, ZeroMemClass.coe_zero, zero_mul]
    · exact exists_rep O O' hO hx hx0
  · rintro ⟨b, s, hs1, hmul⟩
    have hble : O'.valuation (b : F) ≤ 1 := val_le_one_of_isIntegral O O' hO b.2
    have hxv : O'.valuation x * O'.valuation (s : F) = O'.valuation (b : F) := by
      rw [← map_mul, hmul]
    rw [hs1, mul_one] at hxv
    exact O'.mem_of_valuation_le_one x (le_of_eq_of_le hxv hble)

private theorem mem_of_agree [Algebra.IsAlgebraic E F] (O : ValuationSubring E)
    (W₁ W₂ : ValuationSubring F)
    (h₁ : ∀ x : E, algebraMap E F x ∈ W₁ ↔ x ∈ O)
    (h₂ : ∀ x : E, algebraMap E F x ∈ W₂ ↔ x ∈ O)
    (hag : ∀ b : ↥(integralClosure ↥O F), W₁.valuation (b : F) < 1 ↔ W₂.valuation (b : F) < 1)
    {x : F} (hx : x ∈ W₁) : x ∈ W₂ := by
  obtain ⟨b, s, hs1, hmul⟩ := (mem_iff_rep O W₁ h₁ x).mp hx
  have hsle : W₂.valuation (s : F) ≤ 1 := val_le_one_of_isIntegral O W₂ h₂ s.2
  have hs2 : W₂.valuation (s : F) = 1 := by
    rcases lt_or_eq_of_le hsle with hlt | he
    · exfalso
      have := (hag s).mpr hlt
      rw [hs1] at this
      exact lt_irrefl 1 this
    · exact he
  have hble : W₂.valuation (b : F) ≤ 1 := val_le_one_of_isIntegral O W₂ h₂ b.2
  have hxv : W₂.valuation x * W₂.valuation (s : F) = W₂.valuation (b : F) := by
    rw [← map_mul, hmul]
  rw [hs2, mul_one] at hxv
  exact W₂.mem_of_valuation_le_one x (le_of_eq_of_le hxv hble)

end EsbG2bPrufer

private theorem mem_iff_exists_integralClosure_valuation_eq_one_mul_eq
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [Algebra.IsAlgebraic E F]
    (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) :
    (∀ x : F, x ∈ O' ↔ ∃ b s : integralClosure O F, O'.valuation (s : F) = 1 ∧ x * s = b) ∧
    (∀ O'' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) →
      (∀ b : integralClosure O F, O'.valuation (b : F) < 1 ↔
        O''.valuation (b : F) < 1) → O'' = O') := by
  constructor
  · intro x
    exact EsbG2bPrufer.mem_iff_rep O O' hO x
  · intro O'' hO'' hagree
    ext x
    constructor
    · intro hx
      exact EsbG2bPrufer.mem_of_agree O O'' O' hO'' hO (fun b => (hagree b).symm) hx
    · intro hx
      exact EsbG2bPrufer.mem_of_agree O O' O'' hO hO'' hagree hx

namespace HensUniq

open Polynomial IsLocalRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private noncomputable def incl (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) : O →+* V where
  toFun o := ⟨algebraMap K L o, (hV o).mpr o.2⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

@[scoped simp] private lemma incl_apply (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) (o : O) :
    ((incl O V hV o : V) : L) = algebraMap K L o := rfl

private lemma algebraMap_comp_incl (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (algebraMap V L).comp (incl O V hV) = algebraMap O L := by
  ext o
  rfl

private lemma mem_of_isIntegral (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) {x : L} (hx : IsIntegral O x) : x ∈ V := by
  have hx' : IsIntegral V x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (incl O V hV), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, algebraMap_comp_incl]
    exact hpx
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp hx'
  rw [← hy]
  exact y.2

private lemma isUnit_incl_iff (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) (o : O) :
    IsUnit (incl O V hV o) ↔ IsUnit o := by
  constructor
  · intro hu
    by_contra hno
    have ho0 : (o : K) ≠ 0 := by
      intro h0
      have : incl O V hV o = 0 := by
        ext
        simp [h0]
      rw [this] at hu
      exact not_isUnit_zero hu

    have hinvV : (algebraMap K L (o : K))⁻¹ ∈ V := by
      obtain ⟨u, hu'⟩ := hu
      have h1 : (((u⁻¹ : Vˣ) : V) : L) * ((u : V) : L) = 1 := by
        have h := u.inv_mul
        rw [Subtype.ext_iff] at h
        exact h
      have h2 : (((u⁻¹ : Vˣ) : V) : L) = ((u : V) : L)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : ((u : V) : L) = algebraMap K L (o : K) := by
        rw [hu']
        rfl
      rw [← h3, ← h2]
      exact ((u⁻¹ : Vˣ) : V).2
    have hinvO : (o : K)⁻¹ ∈ O := by
      rw [← hV]
      simpa using hinvV
    apply hno
    refine isUnit_iff_exists_inv.mpr ⟨⟨(o : K)⁻¹, hinvO⟩, ?_⟩
    ext
    simp [ho0]
  · intro hu
    exact hu.map _

private lemma incl_mem_maximalIdeal_iff (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) (o : O) :
    incl O V hV o ∈ maximalIdeal V ↔ o ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_incl_iff]

private lemma isIntegral_inv_of_valuation_eq_one (O : ValuationSubring K) [HenselianLocalRing O]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O)
    {s : L} (hs : IsIntegral O s) (hs1 : V.valuation s = 1) : IsIntegral O s⁻¹ := by

  set S : Subalgebra O L := Algebra.adjoin O {s} with hSdef
  haveI : Module.Finite O S := Algebra.finite_adjoin_simple_of_isIntegral hs
  haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  haveI : IsLocalRing S :=
    S17Hens.isLocalRing_of_isDomain_of_moduleFinite (R := O) (S := S)

  have hSle : S ≤ integralClosure O L := by
    refine Algebra.adjoin_le ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (mem_integralClosure_iff O L).mpr hs
  have hSV : ∀ y : S, (y : L) ∈ V := fun y =>
    mem_of_isIntegral O V hV ((mem_integralClosure_iff O L).mp (hSle y.2))

  let φ : S →+* V :=
    { toFun := fun y => ⟨(y : L), hSV y⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hφO : φ.comp (algebraMap O S) = incl O V hV := by
    ext o
    rfl

  let P : Ideal S := Ideal.comap φ (maximalIdeal V)
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime φ (maximalIdeal V)
  have hPO : Ideal.comap (algebraMap O S) P = maximalIdeal O := by
    ext o
    change φ (algebraMap O S o) ∈ maximalIdeal V ↔ _
    rw [show φ (algebraMap O S o) = incl O V hV o from by rw [← hφO]; rfl]
    exact incl_mem_maximalIdeal_iff O V hV o
  have hPmax : P.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P ?_
    rw [Ideal.under_def, hPO]
    exact IsLocalRing.maximalIdeal.isMaximal O
  have hPeq : P = maximalIdeal S := IsLocalRing.eq_maximalIdeal hPmax

  let sS : S := ⟨s, Algebra.self_mem_adjoin_singleton O s⟩
  have hsunit : IsUnit sS := by
    by_contra hns
    have hmem : sS ∈ maximalIdeal S := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact hns
    rw [← hPeq] at hmem
    change φ sS ∈ maximalIdeal V at hmem
    rw [ValuationSubring.valuation_lt_one_iff] at hmem
    change V.valuation s < 1 at hmem
    rw [hs1] at hmem
    exact lt_irrefl _ hmem
  obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hsunit
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs1
    exact zero_ne_one hs1
  have htL : (t : L) = s⁻¹ := by
    have h1 : s * (t : L) = 1 := by
      have := congrArg (fun z : S => (z : L)) ht
      simpa using this
    field_simp
    simpa [mul_comm] using h1
  rw [← htL]
  exact (mem_integralClosure_iff O L).mp (hSle t.2)

private lemma isIntegral_of_mem (O : ValuationSubring K) [HenselianLocalRing O]
    [Algebra.IsAlgebraic K L]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O)
    {x : L} (hx : x ∈ V) : IsIntegral O x := by
  obtain ⟨hfrac, -⟩ :=
    mem_iff_exists_integralClosure_valuation_eq_one_mul_eq O V hV
  obtain ⟨b, s, hs1, hxs⟩ := (hfrac x).mp hx
  have hsint : IsIntegral O (s : L) := (mem_integralClosure_iff O L).mp s.2
  have hbint : IsIntegral O (b : L) := (mem_integralClosure_iff O L).mp b.2
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs1
    exact zero_ne_one hs1
  have hx' : x = (b : L) * (s : L)⁻¹ := by
    rw [← hxs]
    field_simp
  rw [hx']
  exact hbint.mul (isIntegral_inv_of_valuation_eq_one O V hV hsint hs1)

private theorem main (O : ValuationSubring K) [HenselianLocalRing O] [Algebra.IsAlgebraic K L]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (∀ x : L, x ∈ V ↔ IsIntegral O x) ∧
      ∀ V' : ValuationSubring L, (∀ x : K, algebraMap K L x ∈ V' ↔ x ∈ O) → V' = V := by
  have key : ∀ (W : ValuationSubring L), (∀ x : K, algebraMap K L x ∈ W ↔ x ∈ O) →
      ∀ x : L, x ∈ W ↔ IsIntegral O x := fun W hW x =>
    ⟨fun hx => isIntegral_of_mem O W hW hx, fun hx => mem_of_isIntegral O W hW hx⟩
  refine ⟨key V hV, fun V' hV' => ?_⟩
  ext x
  rw [key V' hV' x, key V hV x]

end HensUniq

namespace ValuationSubring

/-- A valuation subring of an algebraic field extension that extends a
Henselian valuation ring is exactly its integral closure, and it is the
unique such extension: membership is integrality over the base ring, and
any two extensions with the same pullback coincide.

This does not assert that an extension exists; it characterizes and
compares extensions that are given. -/
public theorem forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (O : ValuationSubring K) [HenselianLocalRing O]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (∀ x : L, x ∈ V ↔ IsIntegral O x) ∧
      ∀ V' : ValuationSubring L, (∀ x : K, algebraMap K L x ∈ V' ↔ x ∈ O) → V' = V :=
  HensUniq.main O V hV

end ValuationSubring
