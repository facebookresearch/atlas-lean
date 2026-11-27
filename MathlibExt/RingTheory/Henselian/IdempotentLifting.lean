/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Theorems/Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite.lean`
and
`P2M/Sol/S_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite.lean`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RingTheory.Henselian

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.MvPolynomial.Basic
import MathlibExt.RingTheory.Henselian.EtaleLift

/-!
# Lifting idempotents over a Henselian local ring

Over a Henselian local ring `R`, every idempotent of the closed fibre
`S ⧸ 𝔪 S` of a finite `R`-algebra `S` lifts to a unique idempotent of `S`.

For a monic `f : R[X]`, idempotents of `B[X] ⧸ (f)` correspond to `B`-points of
a fixed étale `R`-algebra, so Hensel's lemma for étale algebras lifts an
idempotent over the residue field to one over `R`; evaluating it at an element
of `S` that satisfies `f` gives existence. Uniqueness holds because `𝔪 S` lies
in the Jacobson radical of `S`. Only the lifting theorem is public.
-/

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
      rw [ite_eq_right]
      intro hj
      apply hb
      ext
      exact hj.symm
    · intro hj; exact absurd (Finset.mem_univ _) hj
  · apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right]
    intro hj
    exact h (hj ▸ i.2)

private theorem coeff_poly_fin {n : ℕ} (c : Fin n → T) (i : Fin n) : (poly c).coeff i = c i := by
  rw [coeff_poly, dite_eq_left i.2]

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
  ·
    unfold IsIdempotentElem
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

universe u v

/-- **Idempotents of the closed fibre lift uniquely.** Over a Henselian local
ring `R`, every idempotent of the closed fibre `S ⧸ 𝔪 S` of a finite
`R`-algebra `S`, where `𝔪` is the maximal ideal of `R`, lifts to a unique
idempotent of `S`. -/
theorem HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (ē : S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) (hē : IsIdempotentElem ē) :
    ∃! e : S, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) e = ē :=
  HenselIdem.existsUnique_isIdempotentElem_mk_eq ē hē
