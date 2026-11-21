/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_
moduleFinite_of_henselianLocalRing.lean`
and
`P2M/Sol/S_Algebra_Etale_existsUnique_algHom_baseChange_residueField_eq_of_
moduleFinite_of_henselianLocalRing.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib - https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Tactic
public import MathlibExt.RingTheory.Henselian.EtaleLift

@[expose] public section

universe u v w

open scoped TensorProduct


set_option autoImplicit false

open Polynomial

namespace HenselIdem


section poly

variable {T : Type*} [CommRing T]

noncomputable def poly {n : ℕ} (c : Fin n → T) : T[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

theorem coeff_poly {n : ℕ} (c : Fin n → T) (j : ℕ) :
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

theorem coeff_poly_fin {n : ℕ} (c : Fin n → T) (i : Fin n) : (poly c).coeff i = c i := by
  rw [coeff_poly, dif_pos i.2]

theorem degree_poly_lt {n : ℕ} (c : Fin n → T) : (poly c).degree < n :=
  degree_sum_fin_lt c

theorem poly_coeff_eq_of_degree_lt {n : ℕ} (p : T[X]) (hp : p.degree < n) :
    poly (fun i : Fin n => p.coeff i) = p := by
  ext j
  rw [coeff_poly]
  split_ifs with h
  · rfl
  · symm
    apply coeff_eq_zero_of_degree_lt
    exact lt_of_lt_of_le hp (by exact_mod_cast not_lt.mp h)

theorem poly_map {n : ℕ} (c : Fin n → T) {T' : Type*} [CommRing T'] (φ : T →+* T') :
    (poly c).map φ = poly (fun i => φ (c i)) := by
  unfold poly
  simp [Polynomial.map_sum]

theorem poly_injective {n : ℕ} {c c' : Fin n → T} (h : poly c = poly c') : c = c' := by
  funext i
  rw [← coeff_poly_fin c i, ← coeff_poly_fin c' i, h]

theorem eq_of_dvd_sub_of_degree_lt {F p q : T[X]} (hF : F.Monic)
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

noncomputable def redQuot : AdjoinRoot F →+* AdjoinRoot G :=
  AdjoinRoot.lift ((AdjoinRoot.of G).comp (Ideal.Quotient.mk J)) (AdjoinRoot.root G) (by
    rw [← Polynomial.eval₂_map, hG]
    exact AdjoinRoot.eval₂_root G)

include hG in
theorem redQuot_mk (p : B[X]) :
    redQuot J F G hG (AdjoinRoot.mk F p) = AdjoinRoot.mk G (p.map (Ideal.Quotient.mk J)) := by
  unfold redQuot
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq, ←
    Polynomial.aeval_def,
    AdjoinRoot.aeval_eq]

theorem redQuot_surjective : Function.Surjective (redQuot J F G hG) := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective p
  exact ⟨AdjoinRoot.mk F q, redQuot_mk J F G hG q⟩

theorem ker_redQuot_le :
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

theorem isNilpotent_of_mem_ker_redQuot (hJ : J ^ 2 = ⊥) {x : AdjoinRoot F}
    (hx : x ∈ RingHom.ker (redQuot J F G hG)) : IsNilpotent x := by
  refine ⟨2, ?_⟩
  have h1 : x ∈ J.map (AdjoinRoot.of F) := ker_redQuot_le J F G hG hx
  have h2 : x ^ 2 ∈ (J.map (AdjoinRoot.of F)) ^ 2 := Ideal.pow_mem_pow h1 2
  rw [← Ideal.map_pow, hJ, Ideal.map_bot] at h2
  exact (Ideal.mem_bot).mp h2

end reduction

section scheme

variable {R : Type u} [CommRing R] (f : R[X])

abbrev P : Type u := MvPolynomial (Fin f.natDegree) R

noncomputable def genericElem : (P f)[X] :=
  poly (fun i : Fin f.natDegree => (MvPolynomial.X i : P f))

noncomputable def idemRem : (P f)[X] :=
  (genericElem f * genericElem f - genericElem f) %ₘ (f.map (algebraMap R (P f)))

noncomputable def idemIdeal : Ideal (P f) := Ideal.span (↑(idemRem f).coeffs : Set (P f))

theorem idemIdeal_fg : (idemIdeal f).FG := ⟨(idemRem f).coeffs, rfl⟩

abbrev E : Type u := P f ⧸ idemIdeal f

variable {f}

section points

variable {B : Type*} [CommRing B] [Algebra R B]

noncomputable def elemOf (ψ : P f →ₐ[R] B) : B[X] :=
  poly (fun i : Fin f.natDegree => ψ (MvPolynomial.X i))

theorem genericElem_map (ψ : P f →ₐ[R] B) :
    (genericElem f).map (ψ : P f →+* B) = elemOf ψ := by
  unfold genericElem elemOf
  rw [poly_map]
  rfl

theorem map_algebraMap_map (ψ : P f →ₐ[R] B) :
    (f.map (algebraMap R (P f))).map (ψ : P f →+* B) = f.map (algebraMap R B) := by
  rw [Polynomial.map_map, AlgHom.comp_algebraMap]

theorem idemRem_map (hf : f.Monic) (ψ : P f →ₐ[R] B) :
    (idemRem f).map (ψ : P f →+* B) =
      (elemOf ψ * elemOf ψ - elemOf ψ) %ₘ (f.map (algebraMap R B)) := by
  unfold idemRem
  rw [map_modByMonic _ (hf.map _), Polynomial.map_sub, Polynomial.map_mul, genericElem_map,
    map_algebraMap_map]

theorem forall_idemIdeal_iff (hf : f.Monic) (ψ : P f →ₐ[R] B) :
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

theorem elemOf_comp {B' : Type*} [CommRing B'] [Algebra R B'] (χ : B →ₐ[R] B')
    (ψ : P f →ₐ[R] B) :
    elemOf (χ.comp ψ) = (elemOf ψ).map (χ : B →+* B') := by
  unfold elemOf
  rw [poly_map]
  rfl

theorem degree_elemOf_lt (ψ : P f →ₐ[R] B) : (elemOf ψ).degree < f.natDegree :=
  degree_poly_lt _

theorem degree_map_eq (hf : f.Monic) [Nontrivial B] :
    (f.map (algebraMap R B)).degree = f.natDegree := by
  rw [degree_eq_natDegree (hf.map _).ne_zero, hf.natDegree_map]

theorem apply_X_eq_of_mk_eq (hf : f.Monic) {ψ₁ ψ₂ : P f →ₐ[R] B}
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

noncomputable def evalAt (c : Fin f.natDegree → B) : P f →ₐ[R] B := MvPolynomial.aeval c

theorem evalAt_X (c : Fin f.natDegree → B) (i : Fin f.natDegree) :
    evalAt (f := f) c (MvPolynomial.X i) = c i :=
  MvPolynomial.aeval_X c i

theorem elemOf_evalAt (c : Fin f.natDegree → B) : elemOf (evalAt (f := f) c) = poly c := by
  unfold elemOf
  congr 1
  funext i
  exact evalAt_X c i

theorem forall_idemIdeal_comp_mk (ψ : E f →ₐ[R] B) :
    ∀ a ∈ idemIdeal f, (ψ.comp (Ideal.Quotient.mkₐ R (idemIdeal f))) a = 0 := by
  intro a ha
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

theorem exists_algHom_of_isIdempotentElem (hf : f.Monic)
    (x : AdjoinRoot (f.map (algebraMap R B))) (hx : IsIdempotentElem x) :
    ∃ ψ : E f →ₐ[R] B, AdjoinRoot.mk (f.map (algebraMap R B))
      (elemOf (ψ.comp (Ideal.Quotient.mkₐ R (idemIdeal f)))) = x := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Subsingleton (AdjoinRoot (f.map (algebraMap R B))) :=
      (AdjoinRoot.mk_surjective).subsingleton
    refine ⟨Ideal.Quotient.liftₐ (idemIdeal f) (evalAt (f := f) fun _ => 0) ?_, Subsingleton.elim _
      _⟩
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

theorem formallyEtale_E (hf : f.Monic) : Algebra.FormallyEtale R (E f) := by
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
        (AdjoinRoot.mk (f.map (algebraMap R B)) (elemOf (ψ₁.comp (Ideal.Quotient.mkₐ R (idemIdeal
          f)))) -
          AdjoinRoot.mk (f.map (algebraMap R B)) (elemOf (ψ₂.comp (Ideal.Quotient.mkₐ R (idemIdeal
            f))))) := by
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

theorem etale_E (hf : f.Monic) : Algebra.Etale R (E f) :=
  { formallyEtale := formallyEtale_E hf
    finitePresentation := Algebra.FinitePresentation.quotient (idemIdeal_fg f) }

end scheme

section hensel

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

open IsLocalRing

theorem exists_dvd_and_map_residue_eq {f : R[X]} (hf : f.Monic)
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
      rfl
    rw [h1, h2, elemOf_evalAt, hpoly]

end hensel

section finite

open IsLocalRing

variable {R : Type u} [CommRing R]

theorem exists_isIdempotentElem_of_isArtinianRing {C : Type*} [CommRing C] [IsArtinianRing
  C]
    (c : C) : ∃ (N : ℕ) (d : C), 1 ≤ N ∧ IsIdempotentElem (d * c ^ N) ∧ c ^ N = (d * c ^ N) * c ^ N
      := by
  let g : ℕ →o (Ideal C)ᵒᵈ :=
    ⟨fun k => OrderDual.toDual (Ideal.span {c ^ k}), fun k m hkm =>
      OrderDual.toDual_le_toDual.mpr (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow c
        hkm))⟩
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
  ·
    unfold IsIdempotentElem
    calc d * c ^ N * (d * c ^ N) = d * (d * c ^ (2 * N)) := by ring
      _ = d * c ^ N := by rw [hd]
  · calc c ^ N = d * c ^ (2 * N) := hd.symm
      _ = d * c ^ N * c ^ N := by ring

theorem map_maximalIdeal_le_jacobson [IsLocalRing R] {S : Type*} [CommRing S] [Algebra R S]
    [Module.Finite R S] :
    (maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro 𝔫 ⟨-, h𝔫⟩
  rw [Ideal.map_le_iff_le_comap]
  have : (𝔫.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (algebraMap R S)
      (fun x => Algebra.IsIntegral.isIntegral x) 𝔫
  rw [IsLocalRing.eq_maximalIdeal this]

theorem eq_of_sub_mem_jacobson {S : Type*} [CommRing S] {e₁ e₂ : S}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (h : e₁ - e₂ ∈ Ideal.jacobson (⊥ :
      Ideal S)) :
    e₁ = e₂ := by
  have h3 : (e₁ - e₂) ^ 3 = e₁ - e₂ := by
    have h1 := he₁.eq
    have h2 := he₂.eq
    have : (e₁ - e₂) ^ 3 = e₁ * e₁ * e₁ - 3 * (e₁ * e₁) * e₂ + 3 * e₁ * (e₂ * e₂) - e₂ * e₂ * e₂ :=
      by ring
    rw [this, h1, h1, h2, h2]
    ring
  have hsq : (e₁ - e₂) ^ 2 ∈ Ideal.jacobson (⊥ : Ideal S) := Ideal.pow_mem_of_mem _ h 2 (by
    norm_num)
  have hu : IsUnit ((e₁ - e₂) ^ 2 * (-1) + 1) := Ideal.mem_jacobson_bot.mp hsq (-1)
  have hzero : (e₁ - e₂) * ((e₁ - e₂) ^ 2 * (-1) + 1) = 0 := by
    have : (e₁ - e₂) * ((e₁ - e₂) ^ 2 * (-1) + 1) = (e₁ - e₂) - (e₁ - e₂) ^ 3 := by ring
    rw [this, h3, sub_self]
  have := (IsUnit.mul_left_eq_zero hu).mp hzero
  exact sub_eq_zero.mp this

variable [HenselianLocalRing R]

theorem existsUnique_isIdempotentElem_mk_eq {S : Type*} [CommRing S] [Algebra R S]
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
  ·
    haveI : Subsingleton (S ⧸ 𝔪S) := by
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
  ·
    obtain ⟨t, ht⟩ := hediv
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


open HenselIdem in
private theorem HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (ē : S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) (hē : IsIdempotentElem ē) :
    ∃! e : S, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) e = ē :=
  HenselIdem.existsUnique_isIdempotentElem_mk_eq ē hē

set_option autoImplicit false


section hensSplitHelpers

open IsLocalRing

private theorem hensSplit_comap_map_mk {S : Type v} [CommRing S] {K m : Ideal S} (hK : K ≤ m) :
    (m.map (Ideal.Quotient.mk K)).comap (Ideal.Quotient.mk K) = m := by
  rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hK]

private theorem hensSplit_isMaximal_map_mk {S : Type v} [CommRing S] {K m : Ideal S} (hm :
  m.IsMaximal)
    (hK : K ≤ m) : (m.map (Ideal.Quotient.mk K)).IsMaximal := by
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk K)
    Ideal.Quotient.mk_surjective hm
    with h | h
  · exfalso
    apply hm.ne_top
    rw [← hensSplit_comap_map_mk hK, h, Ideal.comap_top]
  · exact h

private theorem hensSplit_map_maximalIdeal_le {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] (m : Ideal S) (hm : m.IsMaximal) :
    (maximalIdeal R).map (algebraMap R S) ≤ m := by
  rw [Ideal.map_le_iff_le_comap]
  haveI := hm
  have hmax : (m.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
      (fun x => Algebra.IsIntegral.isIntegral x) m
  rw [IsLocalRing.eq_maximalIdeal hmax]

private theorem hensSplit_isArtinianRing_fibre {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  set J : Ideal S := (maximalIdeal R).map (algebraMap R S) with hJ
  let k := R ⧸ maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  have hJR : ∀ r ∈ maximalIdeal R, algebraMap R (S ⧸ J) r = 0 := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  letI : Algebra k (S ⧸ J) := (Ideal.Quotient.lift _ (algebraMap R (S ⧸ J)) hJR).toAlgebra
  haveI : IsScalarTower R k (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Module.Finite k (S ⧸ J) := Module.Finite.of_restrictScalars_finite R k (S ⧸ J)
  exact IsArtinianRing.of_finite k (S ⧸ J)

private theorem hensSplit_finite_maximalSpectrum {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  set J : Ideal S := (maximalIdeal R).map (algebraMap R S) with hJ
  haveI : IsArtinianRing (S ⧸ J) := hensSplit_isArtinianRing_fibre
  let F : MaximalSpectrum S → MaximalSpectrum (S ⧸ J) := fun m =>
    ⟨m.asIdeal.map (Ideal.Quotient.mk J),
      hensSplit_isMaximal_map_mk m.isMaximal (hensSplit_map_maximalIdeal_le (R := R) _ m.isMaximal)⟩
  refine Finite.of_injective F ?_
  intro m₁ m₂ h
  have h2 : (m₁.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) =
      (m₂.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) := by
    have := congrArg MaximalSpectrum.asIdeal h
    simp only [F] at this
    rw [this]
  rw [hensSplit_comap_map_mk (hensSplit_map_maximalIdeal_le (R := R) _ m₁.isMaximal),
    hensSplit_comap_map_mk (hensSplit_map_maximalIdeal_le (R := R) _ m₂.isMaximal)] at h2
  exact MaximalSpectrum.ext h2

private theorem hensSplit_isIdempotentElem_eq_zero_or_one {R : Type u} [CommRing R] [IsLocalRing R]
  {a : R}
    (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · right
    exact h.mul_left_cancel (by rw [mul_one]; exact ha.eq)
  · left
    have : (1 - a) * a = (1 - a) * 0 := by rw [mul_zero, sub_mul, one_mul, ha.eq, sub_self]
    exact h.mul_left_cancel this

private theorem hensSplit_isIdempotentElem_eq_of_mk_eq {R : Type u} [CommRing R]
  [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] {a b : S}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (h : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) a =
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) : a = b :=
  (HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
      (Ideal.Quotient.mk _ a) (ha.map _)).unique ⟨ha, rfl⟩ ⟨hb, h.symm⟩

private theorem hensSplit_isLocalRing_quotient {S : Type v} [CommRing S] (e : S) (m : Ideal S) (hm
  : m.IsMaximal)
    (h1 : 1 - e ∈ m) (h2 : ∀ m' : Ideal S, m'.IsMaximal → m' ≠ m → e ∈ m') :
    IsLocalRing (S ⧸ Ideal.span {1 - e}) := by
  apply IsLocalRing.of_unique_max_ideal
  set K : Ideal S := Ideal.span {1 - e} with hKdef
  have hK : K ≤ m := by
    rw [hKdef, Ideal.span_le, Set.singleton_subset_iff]
    exact h1
  refine ⟨m.map (Ideal.Quotient.mk K), hensSplit_isMaximal_map_mk hm hK, ?_⟩
  intro N hN
  have hNc : (N.comap (Ideal.Quotient.mk K)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have heq : N.comap (Ideal.Quotient.mk K) = m := by
    by_contra hne
    have he : e ∈ N.comap (Ideal.Quotient.mk K) := h2 _ hNc hne
    have hKmem : 1 - e ∈ K := Ideal.subset_span (Set.mem_singleton _)
    have h1e : 1 - e ∈ N.comap (Ideal.Quotient.mk K) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hKmem]
      exact N.zero_mem
    have : (1 : S) ∈ N.comap (Ideal.Quotient.mk K) := by
      have := add_mem h1e he
      rwa [sub_add_cancel] at this
    exact hNc.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  rw [← heq, Ideal.map_comap_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective]

end hensSplitHelpers

private theorem HenselianLocalRing.exists_completeOrthogonalIdempotents_quotient
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    ∃ (_ : Fintype (MaximalSpectrum S)) (e : MaximalSpectrum S → S),
      CompleteOrthogonalIdempotents e ∧
      (∀ m : MaximalSpectrum S, e m ∉ m.asIdeal) ∧
      (∀ m m' : MaximalSpectrum S, m ≠ m' → e m ∈ m'.asIdeal) ∧
      (∀ m : MaximalSpectrum S, IsLocalRing (S ⧸ Ideal.span {1 - e m})) := by
  classical
  haveI : Finite (MaximalSpectrum S) := hensSplit_finite_maximalSpectrum (R := R)
  letI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  haveI : IsArtinianRing (S ⧸ J) := hensSplit_isArtinianRing_fibre
  have hJle : ∀ m : MaximalSpectrum S, J ≤ m.asIdeal := fun m =>
    hensSplit_map_maximalIdeal_le (R := R) m.asIdeal m.isMaximal

  let P : MaximalSpectrum S → Type v := fun m => S ⧸ m.asIdeal
  let π : S →+* (∀ m, P m) := RingHom.pi fun m => Ideal.Quotient.mk m.asIdeal
  have hcop : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum S => m.asIdeal) := by
    intro m m' h
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne m.isMaximal m'.isMaximal
      (fun h' => h (MaximalSpectrum.ext h'))
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop x
    exact ⟨r, funext hr⟩
  have hJπ : ∀ s ∈ J, π s = 0 := by
    intro s hs
    funext m
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJle m hs)
  let ψ : S ⧸ J →+* (∀ m, P m) := Ideal.Quotient.lift J π hJπ
  have hψmk : ∀ s, ψ (Ideal.Quotient.mk J s) = π s := fun s => Ideal.Quotient.lift_mk J π hJπ
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨s, hs⟩ := hπ x
    exact ⟨Ideal.Quotient.mk J s, by rw [hψmk, hs]⟩

  have hnil : ∀ x ∈ RingHom.ker ψ, IsNilpotent x := by
    intro x hx
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hs : ∀ m : MaximalSpectrum S, s ∈ m.asIdeal := by
      intro m
      have h0 : π s = 0 := by rw [← hψmk]; exact hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h0 m)
    have hmem : Ideal.Quotient.mk J s ∈ Ideal.jacobson (⊥ : Ideal (S ⧸ J)) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro N ⟨-, hN⟩
      haveI := hN
      have hNc : (N.comap (Ideal.Quotient.mk J)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      exact hs ⟨_, hNc⟩
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hmem n
    rw [hn] at this
    simpa using this

  have hf : CompleteOrthogonalIdempotents fun m : MaximalSpectrum S => (Pi.single m 1 : ∀ m, P m) :=
    CompleteOrthogonalIdempotents.single P
  obtain ⟨ē, hē, hēf⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker ψ hnil hf (fun m => hψ _)

  have hex := fun m : MaximalSpectrum S =>
    (HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite (ē m) (hē.idem
      m)).exists
  choose e he hemk using hex
  have hπe : ∀ m m' : MaximalSpectrum S,
      Ideal.Quotient.mk m'.asIdeal (e m) = (Pi.single m 1 : ∀ m, P m) m' := by
    intro m m'
    have h1 : π (e m) = Pi.single m 1 := by
      rw [← hψmk, hemk]
      exact congrFun hēf m
    exact congrFun h1 m'
  have hnotMem : ∀ m : MaximalSpectrum S, e m ∉ m.asIdeal := by
    intro m hm
    have h1 := hπe m m
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, Pi.single_eq_same] at h1
    exact m.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp h1)
  have hmem : ∀ m m' : MaximalSpectrum S, m ≠ m' → e m ∈ m'.asIdeal := by
    intro m m' h
    have h1 := hπe m m'
    rw [Pi.single_eq_of_ne (Ne.symm h)] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, ?_⟩
    intro m m' h
    refine hensSplit_isIdempotentElem_eq_of_mk_eq (R := R) ((he m).mul (he m'))
      (IsIdempotentElem.zero) ?_
    rw [map_mul, map_zero, hemk, hemk]
    exact hē.ortho h
  have hcomplete : ∑ m, e m = 1 := by
    refine hensSplit_isIdempotentElem_eq_of_mk_eq (R := R) hortho.isIdempotentElem_sum
      (IsIdempotentElem.one) ?_
    rw [map_sum, map_one]
    simp_rw [hemk]
    exact hē.complete
  refine ⟨inferInstance, e, ⟨hortho, hcomplete⟩, hnotMem, hmem, ?_⟩

  intro m
  refine hensSplit_isLocalRing_quotient (e m) m.asIdeal m.isMaximal ?_ ?_
  · have h1 := hπe m m
    rw [Pi.single_eq_same] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, h1, sub_self]
  · intro m' hm' hne
    exact hmem m ⟨m', hm'⟩ (fun h => hne (congrArg MaximalSpectrum.asIdeal h).symm)

set_option autoImplicit false


open scoped TensorProduct

private theorem Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E : Type v) [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (B : Type w) [CommRing B] [Algebra R B] [Module.Finite R B]
    (φ ψ : E →ₐ[R] B)
    (h : ∀ x : E, φ x - ψ x ∈ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :
    φ = ψ := by
  classical
  set I : Ideal B := Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) with hI

  have hIJ : I ≤ Ideal.jacobson (⊥ : Ideal B) := by
    refine le_sInf fun J hJ => ?_
    obtain ⟨-, hJmax⟩ := hJ
    rw [hI, Ideal.map_le_iff_le_comap]
    have hc : (J.comap (algebraMap R B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R B)
      (fun x => Algebra.IsIntegral.isIntegral x) J
    rw [← IsLocalRing.eq_maximalIdeal hc]

  set e : E ⊗[R] E := Algebra.FormallyUnramified.elem R E with he
  have he1 : ∀ s : E, ((1 : E) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : E)) * e = 0 :=
    fun s => Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem s
  have he2 : Algebra.TensorProduct.lmul' R e = 1 := Algebra.FormallyUnramified.lmul_elem
  set Φ : E ⊗[R] E →ₐ[R] B := Algebra.TensorProduct.productMap φ ψ with hΦ

  have hΦμ : ∀ t : E ⊗[R] E, Φ t - φ (Algebra.TensorProduct.lmul' R t) ∈ I := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
          ← mul_sub]
        refine I.mul_mem_left _ ?_
        have := I.neg_mem (h b)
        rwa [neg_sub] at this
    | add u v hu hv =>
        rw [map_add, map_add, map_add]
        convert I.add_mem hu hv using 1
        ring
  have hΦe : Φ e - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := by
    apply hIJ
    simpa [he2] using hΦμ e
  have hunit : IsUnit (Φ e) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hΦe

  refine AlgHom.ext fun x => ?_
  have hdx : Φ (x ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x) = φ x - ψ x := by
    rw [map_sub, hΦ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul,
      map_one, map_one, mul_one, one_mul]
  have hann : (x ⊗ₜ[R] (1 : E) - (1 : E) ⊗ₜ[R] x) * e = 0 := by
    rw [← neg_sub, neg_mul, he1 x, neg_zero]
  have hkey : (φ x - ψ x) * Φ e = 0 := by
    rw [← hdx, ← map_mul, hann, map_zero]
  exact sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hkey)

set_option autoImplicit false

open scoped TensorProduct


namespace H1Aux

open IsLocalRing

section LocalHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private theorem isLocalHom_algebraMap_of_moduleFinite [IsLocalRing A] [IsLocalRing B]
  [Module.Finite A B] :
    IsLocalHom (algebraMap A B) := by
  refine ((local_hom_TFAE (algebraMap A B)).out 1 4 rfl rfl).mpr ?_
  intro x hx
  rw [Ideal.mem_comap]
  by_contra hxB
  have hu : IsUnit (algebraMap A B x) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hxB

  have htop : (⊤ : Submodule A B) ≤ Ideal.span {x} • (⊤ : Submodule A B) := by
    intro b _
    obtain ⟨u, hu'⟩ := hu
    have : b = x • (↑u⁻¹ * b) := by
      rw [Algebra.smul_def, ← mul_assoc, ← hu', Units.mul_inv, one_mul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) Submodule.mem_top
  have hjac : Ideal.span {x} ≤ (⊥ : Ideal A).jacobson :=
    (Ideal.span_singleton_le_iff_mem _).mpr (maximalIdeal_le_jacobson ⊥ hx)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) ⊤
    Module.Finite.fg_top htop hjac
  exact one_ne_zero ((Submodule.eq_bot_iff _).mp hbot 1 Submodule.mem_top)

private theorem restrictScalars_maximalIdeal_le_smul_top [IsLocalRing A] [IsLocalRing B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ((maximalIdeal B).restrictScalars A : Submodule A B) ≤ maximalIdeal A • (⊤ : Submodule A B) :=
      by
  rw [Ideal.smul_top_eq_map, h]

end LocalHom

section Residue

variable {R : Type u} [CommRing R] [IsLocalRing R] {C : Type w} [CommRing C] [Algebra R C]

private theorem one_tmul_eq_zero_iff (c : C) :
    (1 : ResidueField R) ⊗ₜ[R] c = 0 ↔ c ∈ (maximalIdeal R).map (algebraMap R C) := by
  have h1 : (1 : ResidueField R) ⊗ₜ[R] c = 0 ↔ c ⊗ₜ[R] (1 : ResidueField R) = 0 := by
    rw [← (Algebra.TensorProduct.comm R (ResidueField R) C).injective.eq_iff, map_zero,
      Algebra.TensorProduct.comm_tmul]
  have h2 : c ∈ (maximalIdeal R).map (algebraMap R C) ↔ c ⊗ₜ[R] (1 : ResidueField R) = 0 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem,
      ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (maximalIdeal R)).injective.eq_iff,
        map_zero,
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rfl
  exact h1.trans h2.symm

private theorem exists_one_tmul (z : ResidueField R ⊗[R] C) : ∃ c : C, z = (1 : ResidueField R)
  ⊗ₜ[R] c := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [TensorProduct.tmul_zero]⟩
  | tmul a c =>
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    refine ⟨r • c, ?_⟩
    rw [show IsLocalRing.residue R r = r • (1 : ResidueField R) from Algebra.algebraMap_eq_smul_one
      r,
      TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', by rw [TensorProduct.tmul_add]⟩

variable [IsLocalRing C] [IsLocalHom (algebraMap R C)]

private theorem nontrivial_residueField_tensor : Nontrivial (ResidueField R ⊗[R] C) := by
  refine ⟨⟨(1 : ResidueField R) ⊗ₜ[R] (1 : C), 0, ?_⟩⟩
  rw [Ne, one_tmul_eq_zero_iff]
  intro h
  have hle : (maximalIdeal R).map (algebraMap R C) ≤ maximalIdeal C :=
    ((local_hom_TFAE (algebraMap R C)).out 1 3 rfl rfl).mp ‹_›
  exact (maximalIdeal.isMaximal C).ne_top (Ideal.eq_top_of_isUnit_mem _ (hle h) isUnit_one)

private theorem isLocalRing_residueField_tensor : IsLocalRing (ResidueField R ⊗[R] C) := by
  haveI := nontrivial_residueField_tensor (R := R) (C := C)
  refine IsLocalRing.of_surjective'
    (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := C) : C →+*
      ResidueField R ⊗[R] C) ?_
  intro z
  obtain ⟨c, rfl⟩ := exists_one_tmul z
  exact ⟨c, rfl⟩

end Residue

end H1Aux

namespace H1Aux

open IsLocalRing

section Core

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {O : Type v} [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
  {C : Type w} [CommRing C] [Algebra R C] [Module.Finite R C]

private theorem algHom_eq_of_map_eq (ψ₁ ψ₂ : O →ₐ[R] C)
    (h : Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ₁ =
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ₂) : ψ₁ = ψ₂ := by
  apply Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing R O C
  intro x
  rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, sub_eq_zero]
  have := AlgHom.congr_fun h ((1 : ResidueField R) ⊗ₜ[R] x)
  simpa [Algebra.TensorProduct.map_tmul] using this

private theorem exists_algHom_of_isLocalRing [IsLocalRing C]
    (ψbar : ResidueField R ⊗[R] O →ₐ[ResidueField R] ResidueField R ⊗[R] C) :
    ∃ ψ : O →ₐ[R] C, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ =
      ψbar := by
  classical
  haveI : IsLocalHom (algebraMap R C) := isLocalHom_algebraMap_of_moduleFinite

  let f₀ : ResidueField R →ₐ[R] ResidueField C :=
    { toRingHom := ResidueField.map (algebraMap R C), commutes' := fun r => rfl }
  let θ : ResidueField R ⊗[R] C →ₐ[R] ResidueField C :=
    Algebra.TensorProduct.lift f₀ (IsScalarTower.toAlgHom R C (ResidueField C)) (fun _ _ =>
      Commute.all _ _)
  have hθ : ∀ (a : ResidueField R) (c : C), θ (a ⊗ₜ[R] c) = f₀ a * residue C c :=
    fun a c => Algebra.TensorProduct.lift_tmul _ _ _ a c

  let q : O →ₐ[R] ResidueField C :=
    θ.comp ((ψbar.restrictScalars R).comp (Algebra.TensorProduct.includeRight (A := ResidueField
      R)))
  let pbar : C ⊗[R] O →ₐ[C] ResidueField C :=
    Algebra.TensorProduct.lift (Algebra.ofId C (ResidueField C)) q (fun _ _ => Commute.all _ _)
  have hpbar : ∀ (c : C) (o : O), pbar (c ⊗ₜ[R] o) = residue C c * q o :=
    fun c o => Algebra.TensorProduct.lift_tmul _ _ _ c o
  have hpsurj : Function.Surjective pbar := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective (R := C) x
    exact ⟨c ⊗ₜ 1, by rw [hpbar, map_one, mul_one]⟩

  obtain ⟨hfin, e, hce, hnot, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_quotient
      (R := R) (S := C ⊗[R] O)
  let m₀ : MaximalSpectrum (C ⊗[R] O) :=
    ⟨RingHom.ker (pbar : C ⊗[R] O →+* ResidueField C), RingHom.ker_isMaximal_of_surjective _ hpsurj⟩
  have he₀ : pbar (e m₀) = 1 := by
    have hne : pbar (e m₀) ≠ 0 := fun h => hnot m₀ (by
      show e m₀ ∈ RingHom.ker (pbar : C ⊗[R] O →+* ResidueField C)
      rwa [RingHom.mem_ker])
    have hid : IsIdempotentElem (pbar (e m₀)) := (hce.idem m₀).map pbar
    exact (IsIdempotentElem.iff_eq_zero_or_one.mp hid).resolve_left hne
  let I : Ideal (C ⊗[R] O) := Ideal.span {1 - e m₀}
  haveI hL : IsLocalRing ((C ⊗[R] O) ⧸ I) := hloc m₀

  haveI : IsLocalHom (algebraMap C ((C ⊗[R] O) ⧸ I)) :=
    isLocalHom_algebraMap_of_moduleFinite (A := C) (B := (C ⊗[R] O) ⧸ I)
  haveI : Algebra.FormallyUnramified C ((C ⊗[R] O) ⧸ I) := Algebra.FormallyUnramified.quotient I

  haveI : Module.Flat C ((C ⊗[R] O) ⧸ I) := by
    let r : (C ⊗[R] O) →ₗ[C] ((C ⊗[R] O) ⧸ I) := (Ideal.Quotient.mkₐ C I).toLinearMap
    let i₀ : ((C ⊗[R] O) ⧸ I.restrictScalars C) →ₗ[C] (C ⊗[R] O) :=
      (I.restrictScalars C).liftQ (LinearMap.mulLeft C (e m₀)) (by
        intro x hx
        rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hx
        obtain ⟨y, rfl⟩ := hx
        rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, ← mul_assoc, (hce.idem
          m₀).mul_one_sub_self, zero_mul])
    let i : ((C ⊗[R] O) ⧸ I) →ₗ[C] (C ⊗[R] O) :=
      i₀ ∘ₗ (Submodule.Quotient.restrictScalarsEquiv C I).symm.toLinearMap
    refine Module.Flat.of_retract i r ?_
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk I (i₀ ((Submodule.Quotient.restrictScalarsEquiv C I).symm
      (Ideal.Quotient.mk I x))) =
      Ideal.Quotient.mk I x
    rw [show (Submodule.Quotient.restrictScalarsEquiv C I).symm (Ideal.Quotient.mk I x) =
        Submodule.Quotient.mk x from rfl]
    show Ideal.Quotient.mk I (e m₀ * x) = Ideal.Quotient.mk I x
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-x, by ring⟩
  haveI : Module.Free C ((C ⊗[R] O) ⧸ I) := Module.free_of_flat_of_isLocalRing
  have hmL := Algebra.FormallyUnramified.map_maximalIdeal (R := C) (S := (C ⊗[R] O) ⧸ I)

  let pL : ((C ⊗[R] O) ⧸ I) →ₐ[C] ResidueField C := Ideal.Quotient.liftₐ I pbar (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_sub, map_one, he₀, sub_self, zero_mul])
  have hpL : ∀ d, pL (Ideal.Quotient.mk I d) = pbar d := fun d => rfl
  have hpLsurj : Function.Surjective pL := by
    intro x
    obtain ⟨d, rfl⟩ := hpsurj x
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  let ιₐ : C →ₐ[C] ((C ⊗[R] O) ⧸ I) := Algebra.ofId C ((C ⊗[R] O) ⧸ I)

  have hιsurj : Function.Surjective ιₐ := by
    have key : (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) ≤ LinearMap.range ιₐ.toLinearMap ⊔
        (maximalIdeal ((C ⊗[R] O) ⧸ I)).restrictScalars C := by
      intro ℓ _
      obtain ⟨c, hc⟩ := residue_surjective (R := C) (pL ℓ)
      have hmem : ℓ - ιₐ c ∈ maximalIdeal ((C ⊗[R] O) ⧸ I) := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply (hu.map pL).ne_zero
        rw [map_sub, sub_eq_zero, ← hc]
        exact (pL.commutes c).symm
      exact Submodule.mem_sup.mpr ⟨ιₐ c, ⟨c, rfl⟩, ℓ - ιₐ c, hmem, by abel⟩
    have hsmul : ((maximalIdeal ((C ⊗[R] O) ⧸ I)).restrictScalars C : Submodule C ((C ⊗[R] O) ⧸ I))
      ≤
        maximalIdeal C • (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) :=
      restrictScalars_maximalIdeal_le_smul_top (A := C) (B := (C ⊗[R] O) ⧸ I) hmL
    have hle : (⊤ : Submodule C ((C ⊗[R] O) ⧸ I)) ≤ LinearMap.range ιₐ.toLinearMap :=
      Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
        (key.trans (sup_le_sup_left hsmul _))
    intro ℓ
    obtain ⟨c, hc⟩ := hle (Submodule.mem_top : ℓ ∈ ⊤)
    exact ⟨c, hc⟩

  have hιinj : Function.Injective ιₐ := by
    let b := Module.Free.chooseBasis C ((C ⊗[R] O) ⧸ I)
    obtain ⟨i₀⟩ := b.index_nonempty
    let g : C →ₗ[C] C := (b.coord i₀) ∘ₗ ιₐ.toLinearMap
    have hg : Function.Surjective g := by
      intro t
      obtain ⟨c, hc⟩ := hιsurj (t • b i₀)
      refine ⟨c, ?_⟩
      show b.coord i₀ (ιₐ c) = t
      rw [hc, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul,
        mul_one]
    have hginj := OrzechProperty.injective_of_surjective_endomorphism g hg
    intro x y hxy
    apply hginj
    show b.coord i₀ (ιₐ x) = b.coord i₀ (ιₐ y)
    rw [hxy]

  let E : C ≃ₐ[C] ((C ⊗[R] O) ⧸ I) := AlgEquiv.ofBijective ιₐ ⟨hιinj, hιsurj⟩
  let σ : (C ⊗[R] O) →ₐ[C] C := (E.symm : ((C ⊗[R] O) ⧸ I) →ₐ[C] C).comp (Ideal.Quotient.mkₐ C I)
  have hEσ : ∀ d, E (σ d) = Ideal.Quotient.mk I d := fun d => E.apply_symm_apply _
  have hσ : ∀ d, residue C (σ d) = pbar d := by
    intro d
    rw [← hpL, ← hEσ]
    show _ = pL (ιₐ (σ d))
    exact (pL.commutes (σ d)).symm
  let ψ : O →ₐ[R] C := (σ.restrictScalars R).comp (Algebra.TensorProduct.includeRight (A := C))
  have hψ : ∀ o, residue C (ψ o) = q o := by
    intro o
    show residue C (σ (1 ⊗ₜ o)) = q o
    rw [hσ, hpbar, map_one, one_mul]
  refine ⟨ψ, ?_⟩

  haveI : IsLocalRing (ResidueField R ⊗[R] C) := isLocalRing_residueField_tensor
  haveI : IsArtinianRing (ResidueField R ⊗[R] C) := IsArtinianRing.of_finite (ResidueField R) _
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective (R := C) x
    exact ⟨1 ⊗ₜ c, by rw [hθ, map_one, one_mul]⟩
  have hnil : IsNilpotent (RingHom.ker (θ : ResidueField R ⊗[R] C →+* ResidueField C)) := by
    rw [ker_eq_maximalIdeal (θ : ResidueField R ⊗[R] C →+* ResidueField C) hθsurj,
      ← jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  apply Algebra.FormallyUnramified.ext' (θ : ResidueField R ⊗[R] C →+* ResidueField C) hnil
  intro z
  suffices hcomp : θ.comp ((Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R))
    ψ).restrictScalars R) =
      θ.comp (ψbar.restrictScalars R) from AlgHom.congr_fun hcomp z
  apply Algebra.TensorProduct.ext'
  intro a o
  have hz : a ⊗ₜ[R] o = algebraMap (ResidueField R) (ResidueField R ⊗[R] O) a * ((1 : ResidueField
    R) ⊗ₜ[R] o) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  show θ (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ (a ⊗ₜ[R] o)) =
    θ (ψbar (a ⊗ₜ[R] o))
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hθ, hψ, hz, map_mul, AlgHom.commutes,
    map_mul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hθ, map_one,
      mul_one]
  rfl

end Core

end H1Aux

namespace H1Aux

open IsLocalRing

section Assemble

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  {O : Type v} [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
  {C : Type w} [CommRing C] [Algebra R C] [Module.Finite R C]

omit [HenselianLocalRing R] [Module.Finite R C] in
private theorem mul_mem_map_maximalIdeal_of_mk_mem [IsLocalRing R] (e c : C) (he : IsIdempotentElem
  e)
    (h : Ideal.Quotient.mk (Ideal.span {1 - e}) c ∈
      (maximalIdeal R).map (algebraMap R (C ⧸ Ideal.span {1 - e}))) :
    c * e ∈ (maximalIdeal R).map (algebraMap R C) := by
  rw [IsScalarTower.algebraMap_eq R C (C ⧸ Ideal.span {1 - e}), ← Ideal.map_map,
    Ideal.Quotient.algebraMap_eq,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
  obtain ⟨c', hc', hcc'⟩ := h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hcc'
  obtain ⟨d, hd⟩ := hcc'
  have : c * e = c' * e := by
    calc c * e = (c' - (c' - c)) * e := by ring
      _ = (c' - (1 - e) * d) * e := by rw [hd]
      _ = c' * e - d * ((1 - e) * e) := by ring
      _ = c' * e := by rw [he.one_sub_mul_self, mul_zero, sub_zero]
  rw [this]
  exact Ideal.mul_mem_right _ _ hc'

omit [Module.Finite R O] [Algebra.Etale R O] [Module.Finite R C] in
private theorem eq_zero_of_forall_map_mk_eq_zero {ι : Type*} [Fintype ι] (e : ι → C)
    (hce : CompleteOrthogonalIdempotents e) (z : ResidueField R ⊗[R] C)
    (hz : ∀ i, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R))
      (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) z = 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := exists_one_tmul z
  rw [one_tmul_eq_zero_iff]
  have hi : ∀ i, c * e i ∈ (maximalIdeal R).map (algebraMap R C) := by
    intro i
    have h := hz i
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
      one_tmul_eq_zero_iff] at h
    exact mul_mem_map_maximalIdeal_of_mk_mem (R := R) (e i) c (hce.idem i) h
  have hc : c = ∑ i, c * e i := by rw [← Finset.mul_sum, hce.complete, mul_one]
  rw [hc]
  exact Ideal.sum_mem _ fun i _ => hi i

private theorem exists_algHom
    (ψbar : ResidueField R ⊗[R] O →ₐ[ResidueField R] ResidueField R ⊗[R] C) :
    ∃ ψ : O →ₐ[R] C, Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ =
      ψbar := by
  classical
  obtain ⟨hfin, e, hce, -, -, hloc⟩ :=
    HenselianLocalRing.exists_completeOrthogonalIdempotents_quotient
      (R := R) (S := C)

  let Cq : MaximalSpectrum C → Type w := fun m => C ⧸ Ideal.span {1 - e m}
  let π : (m : MaximalSpectrum C) → (C →ₐ[R] Cq m) :=
    fun m => Ideal.Quotient.mkₐ R (Ideal.span {1 - e m})
  have hψm : ∀ m, ∃ ψm : O →ₐ[R] Cq m,
      Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψm =
        (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) (π m)).comp ψbar
          := by
    intro m
    haveI : IsLocalRing (Cq m) := hloc m
    haveI : Module.Finite R (Cq m) := inferInstance
    exact exists_algHom_of_isLocalRing _
  choose ψm hψm using hψm

  let Φ : C →ₐ[R] ((m : MaximalSpectrum C) → Cq m) := Pi.algHom R Cq π
  have hΦ : Function.Bijective Φ := by
    have := CompleteOrthogonalIdempotents.bijective_pi hce
    exact this
  let EΦ : C ≃ₐ[R] ((m : MaximalSpectrum C) → Cq m) := AlgEquiv.ofBijective Φ hΦ
  let ψ : O →ₐ[R] C := (EΦ.symm : ((m : MaximalSpectrum C) → Cq m) →ₐ[R] C).comp (Pi.algHom R Cq ψm)
  have hπψ : ∀ m, (π m).comp ψ = ψm m := by
    intro m
    apply AlgHom.ext
    intro o
    show (Φ (EΦ.symm (Pi.algHom R Cq ψm o))) m = ψm m o
    rw [show Φ (EΦ.symm (Pi.algHom R Cq ψm o)) = Pi.algHom R Cq ψm o from EΦ.apply_symm_apply _]
    rfl
  refine ⟨ψ, ?_⟩
  apply AlgHom.ext
  intro x
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_map_mk_eq_zero e hce
  intro m
  rw [map_sub, sub_eq_zero]
  show (Algebra.TensorProduct.map (AlgHom.id _ _) (π m)).comp
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) ψ) x =
    (Algebra.TensorProduct.map (AlgHom.id _ _) (π m)).comp ψbar x
  rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, hπψ, hψm]

end Assemble

end H1Aux

namespace Algebra.Etale

/-- Over a Henselian local ring `R`, a map between the residue-field base
changes of a finite étale `R`-algebra `O` and a finite `R`-algebra `C`
lifts to a unique `R`-algebra map `O →ₐ[R] C`. The target `C` is not
assumed étale or local. -/
theorem existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (O : Type v) [CommRing O] [Algebra R O] [Module.Finite R O] [Algebra.Etale R O]
    (C : Type w) [CommRing C] [Algebra R C] [Module.Finite R C]
    (ψbar : IsLocalRing.ResidueField R ⊗[R] O →ₐ[IsLocalRing.ResidueField R]
      IsLocalRing.ResidueField R ⊗[R] C) :
    ∃! ψ : O →ₐ[R] C,
      Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField
        R)) ψ = ψbar := by
  refine ⟨(H1Aux.exists_algHom ψbar).choose, (H1Aux.exists_algHom ψbar).choose_spec, ?_⟩
  intro ψ' hψ'
  exact H1Aux.algHom_eq_of_map_eq _ _ (hψ'.trans (H1Aux.exists_algHom ψbar).choose_spec.symm)

end Algebra.Etale
