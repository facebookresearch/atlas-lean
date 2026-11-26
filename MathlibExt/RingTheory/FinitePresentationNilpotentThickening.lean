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
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FinitePresentation_of_surjective_of_isNilpotent_ker_
of_flat_of_finitePresentation.lean`
and
`P2M/Sol/S_Algebra_FinitePresentation_of_surjective_of_isNilpotent_ker_
of_flat_of_finitePresentation.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

universe u v w

open Module MvPolynomial


private theorem kill {P : Type u} [CommRing P] (I : Ideal P) (hI : IsNilpotent I)
    {X : Type v} [AddCommGroup X] [Module P X] (S : Submodule P X) (hS : S ≤ I • S) : S = ⊥ := by
  obtain ⟨k, hk⟩ := hI
  have : ∀ j : ℕ, S ≤ I ^ j • S := by
    intro j; induction j with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ j ih =>
      calc S ≤ I ^ j • S := ih
        _ ≤ I ^ j • (I • S) := Submodule.smul_mono le_rfl hS
        _ = I ^ (j + 1) • S := by rw [← Submodule.mul_smul, ← pow_succ]
  have h := this k
  rw [hk, Submodule.zero_eq_bot, Submodule.bot_smul] at h
  exact le_bot_iff.mp h

private theorem eq_top_of_le_sup_smul {P : Type u} [CommRing P] (I : Ideal P) (hI : IsNilpotent I)
    {X : Type v} [AddCommGroup X] [Module P X] (S : Submodule P X) (hS : (⊤ : Submodule P X) ≤ S ⊔
      I • ⊤) : S = ⊤ := by
  have hC : (⊤ : Submodule P (X ⧸ S)) ≤ I • ⊤ := by
    rintro c -
    obtain ⟨x, rfl⟩ := S.mkQ_surjective c
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (hS (Submodule.mem_top : x ∈ ⊤))
    have hz : S.mkQ s = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hs
    rw [map_add, hz, zero_add]
    have := Submodule.mem_map_of_mem (f := S.mkQ) ht
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have htop := kill I hI ⊤ hC
  rw [eq_top_iff]
  intro x _
  have : S.mkQ x ∈ (⊤ : Submodule P (X ⧸ S)) := Submodule.mem_top
  rw [htop, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this

private theorem ker_inf_smul_top {P : Type u} [CommRing P] (I : Ideal P)
    {F : Type v} {A : Type w} [AddCommGroup F] [Module P F] [AddCommGroup A] [Module P A]
      [Module.Flat P A]
    (f : F →ₗ[P] A) (hf : Function.Surjective f) :
    LinearMap.ker f ⊓ (I • ⊤ : Submodule P F) = I • LinearMap.ker f := by
  classical
  refine le_antisymm ?_ (le_inf (Submodule.smul_le_right) (Submodule.smul_mono le_rfl le_top))
  rintro m ⟨hm, hmI⟩
  have hm0 : f m = 0 := hm
  have hmI' : m ∈ I • Submodule.span P (Set.range (id : F → F)) := by
    rw [Set.range_id, Submodule.span_univ]; exact hmI
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I (id : F → F) m).mp hmI'
  have hsum' : ∑ x ∈ a.support, a x • x = m := by simpa [Finsupp.sum] using hsum
  have hrel : ∑ x : ↥a.support, a x • f (x : F) = 0 := by
    have : ∑ x ∈ a.support, a x • f x = f m := by
      rw [← hsum', map_sum]; simp only [map_smul]
    rw [Finset.sum_coe_sort a.support (fun x => a x • f x), this, hm0]
  obtain ⟨kk, b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose m' hm' using fun j => hf (y j)
  have hker : ∀ x : ↥a.support, (x : F) - ∑ j, b x j • m' j ∈ LinearMap.ker f := by
    intro x
    rw [LinearMap.mem_ker, map_sub, map_sum]
    simp only [map_smul, hm']
    have := hy x; simp only at this
    rw [← this, sub_self]
  have hm_eq : m = ∑ x : ↥a.support, a x • ((x : F) - ∑ j, b x j • m' j) := by
    have hz : ∑ x : ↥a.support, a x • ∑ j, b x j • m' j = 0 := by
      calc ∑ x : ↥a.support, a x • ∑ j, b x j • m' j
          = ∑ j, (∑ x : ↥a.support, a x * b x j) • m' j := by
            simp only [Finset.smul_sum, smul_smul]
            rw [Finset.sum_comm]
            simp only [Finset.sum_smul]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            have hbj := hb j
            simp only at hbj
            rw [hbj, zero_smul]
    calc m = ∑ x ∈ a.support, a x • x := hsum'.symm
      _ = ∑ x : ↥a.support, a x • (x : F) := (Finset.sum_coe_sort a.support (fun x => a x • x)).symm
      _ = ∑ x : ↥a.support, a x • (x : F) - ∑ x : ↥a.support, a x • ∑ j, b x j • m' j := by rw [hz,
        sub_zero]
      _ = ∑ x : ↥a.support, a x • ((x : F) - ∑ j, b x j • m' j) := by
            rw [← Finset.sum_sub_distrib]; simp only [smul_sub]
  rw [hm_eq]
  exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem_smul (ha x) (hker x)


namespace Algebra.FinitePresentation

/-- **Finite presentation lifts along a nilpotent thickening of flat algebras.** Let $P$, $B'$,
$A$ and $A'$ be commutative rings. Let $p \colon P \to B'$ be a surjective ring homomorphism with
nilpotent kernel, let $A$ be a flat $P$-algebra with structure map $\iota \colon P \to A$, let
$A'$ be a $B'$-algebra with structure map $\iota' \colon B' \to A'$, and let $q \colon A \to A'$ be
a surjective ring homomorphism such that the square commutes, $q \circ \iota = \iota' \circ p$,
and $\ker q = (\ker p)A$ is the ideal of $A$ generated by $\iota(\ker p)$. If $A'$ is finitely
presented over $B'$, then $A$ is finitely presented over $P$. -/
public theorem of_surjective_of_isNilpotent_ker_of_flat_of_finitePresentation
    {P B' : Type u} [CommRing P] [CommRing B'] (p : P →+* B') (hp : Function.Surjective p)
    (hI : IsNilpotent (RingHom.ker p))
    {A : Type v} [CommRing A] [Algebra P A] [Module.Flat P A]
    {A' : Type w} [CommRing A'] [Algebra B' A']
    (q : A →+* A') (hq : Function.Surjective q)
    (hcomm : q.comp (algebraMap P A) = (algebraMap B' A').comp p)
    (hker : RingHom.ker q = (RingHom.ker p).map (algebraMap P A))
    (hfp' : Algebra.FinitePresentation B' A') :
    Algebra.FinitePresentation P A := by
  classical
  set I : Ideal P := RingHom.ker p with hIdef
  obtain ⟨n, f', hf's, hf'k⟩ := hfp'.out
  choose α hα using fun i : Fin n => hq (f' (MvPolynomial.X i))
  let ψ : MvPolynomial (Fin n) P →ₐ[P] A := MvPolynomial.aeval α
  have hcommr : ∀ r : P, q (algebraMap P A r) = algebraMap B' A' (p r) := fun r =>
    congrArg (fun φ : P →+* A' => φ r) hcomm
  have hsqhom : q.comp (ψ : MvPolynomial (Fin n) P →+* A) =
      (f' : MvPolynomial (Fin n) B' →+* A').comp (MvPolynomial.map p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C, AlgHom.coe_toRingHom]
      rw [MvPolynomial.aeval_C, hcommr, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X, AlgHom.coe_toRingHom]
      rw [MvPolynomial.aeval_X, hα]
  have hsq : ∀ g, q (ψ g) = f' (MvPolynomial.map p g) := fun g =>
    congrArg (fun φ : MvPolynomial (Fin n) P →+* A' => φ g) hsqhom
  have hψs : Function.Surjective ψ := by
    have key : (⊤ : Submodule P A) ≤ LinearMap.range ψ.toLinearMap ⊔ I • ⊤ := by
      rintro x -
      obtain ⟨g', hg'⟩ := hf's (q x)
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective p hp g'
      have h1 : x - ψ g ∈ RingHom.ker q := by
        rw [RingHom.mem_ker, map_sub, hsq, hg', sub_self]
      rw [hker] at h1
      have hx : x - ψ g ∈ I • (⊤ : Submodule P A) := by rw [Ideal.smul_top_eq_map]; exact h1
      have e : x = ψ g + (x - ψ g) := by ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨g, rfl⟩) (Submodule.mem_sup_right hx)
    have htop := eq_top_of_le_sup_smul I hI _ key
    intro x
    have hx : x ∈ LinearMap.range ψ.toLinearMap := by rw [htop]; exact Submodule.mem_top
    exact hx
  let J : Ideal (MvPolynomial (Fin n) P) := RingHom.ker (ψ : MvPolynomial (Fin n) P →+* A)
  have hsmulF : I • (⊤ : Submodule P (MvPolynomial (Fin n) P)) =
      (RingHom.ker (MvPolynomial.map (σ := Fin n) p)).restrictScalars P := by
    rw [MvPolynomial.ker_map, Ideal.smul_top_eq_map, MvPolynomial.algebraMap_eq]
  have hmapJ : Ideal.map (MvPolynomial.map p) J = RingHom.ker (f' : MvPolynomial (Fin n) B' →+* A')
    := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro j hj
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have e1 : (f' : MvPolynomial (Fin n) B' →+* A') (MvPolynomial.map p j) = f' (MvPolynomial.map
        p j) := rfl
      rw [e1, ← hsq, show ψ j = 0 from hj, map_zero]
    · intro y hy
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective p hp y
      have h1 : ψ g ∈ RingHom.ker q := by rw [RingHom.mem_ker, hsq]; exact hy
      rw [hker] at h1
      have h2 : ψ g ∈ I • (⊤ : Submodule P A) := by rw [Ideal.smul_top_eq_map]; exact h1
      have h3 : I • (⊤ : Submodule P A) = (I • (⊤ : Submodule P (MvPolynomial (Fin n) P))).map
        ψ.toLinearMap := by
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hψs]
      rw [h3] at h2
      obtain ⟨h, hh, hψh⟩ := h2
      have hgh : g - h ∈ J := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero]
        exact hψh.symm
      have hmaph : MvPolynomial.map p h = 0 := by
        rw [hsmulF] at hh; exact hh
      have e : MvPolynomial.map p g = MvPolynomial.map p (g - h) := by rw [map_sub, hmaph, sub_zero]
      rw [e]; exact Ideal.mem_map_of_mem _ hgh
  have hFG : (Ideal.map (MvPolynomial.map p) J).FG := by rw [hmapJ]; exact hf'k
  obtain ⟨T, hT⟩ := hFG
  have hlift : ∀ t : ↥T, ∃ j ∈ J, MvPolynomial.map p j = (t : MvPolynomial (Fin n) B') := by
    intro t
    have : (t : MvPolynomial (Fin n) B') ∈ Ideal.map (MvPolynomial.map p) J := hT ▸
      Ideal.subset_span t.2
    exact (Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective p hp)).mp this
  choose lift hliftJ hliftmap using hlift
  let J₀ : Ideal (MvPolynomial (Fin n) P) := Ideal.span (Set.range lift)
  have hJ₀le : J₀ ≤ J := Ideal.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hliftJ t)
  have hmapJ₀ : Ideal.map (MvPolynomial.map p) J₀ = Ideal.map (MvPolynomial.map p) J := by
    apply le_antisymm (Ideal.map_mono hJ₀le)
    rw [← hT]
    apply Ideal.span_le.mpr
    intro t ht
    have : MvPolynomial.map p (lift ⟨t, ht⟩) ∈ Ideal.map (MvPolynomial.map p) J₀ :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨⟨t, ht⟩, rfl⟩)
    rwa [hliftmap ⟨t, ht⟩] at this
  have hkereq : LinearMap.ker ψ.toLinearMap = J.restrictScalars P := by
    ext x; rfl
  have hRL : J.restrictScalars P ⊓ I • (⊤ : Submodule P (MvPolynomial (Fin n) P)) = I •
    J.restrictScalars P := by
    rw [← hkereq]; exact ker_inf_smul_top I ψ.toLinearMap hψs
  have hJle : J.restrictScalars P ≤ J₀.restrictScalars P ⊔ I • J.restrictScalars P := by
    intro j hj
    have hj' : (j : MvPolynomial (Fin n) P) ∈ J := hj
    have : MvPolynomial.map p j ∈ Ideal.map (MvPolynomial.map p) J₀ := by
      rw [hmapJ₀]; exact Ideal.mem_map_of_mem _ hj'
    obtain ⟨j₀, hj₀, hj₀map⟩ := (Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective p
      hp)).mp this
    have hdiff : j - j₀ ∈ RingHom.ker (MvPolynomial.map (σ := Fin n) p) := by
      rw [RingHom.mem_ker, map_sub, hj₀map, sub_self]
    have hdiffI : j - j₀ ∈ I • (⊤ : Submodule P (MvPolynomial (Fin n) P)) := by rw [hsmulF]; exact
      hdiff
    have hdiffJ : j - j₀ ∈ J.restrictScalars P := J.sub_mem hj' (hJ₀le hj₀)
    have hmem : j - j₀ ∈ I • J.restrictScalars P := by rw [← hRL]; exact ⟨hdiffJ, hdiffI⟩
    have e : j = j₀ + (j - j₀) := by ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hj₀) (Submodule.mem_sup_right hmem)
  have hJeq : J = J₀ := by
    apply le_antisymm _ hJ₀le
    obtain ⟨k, hk⟩ := hI
    have hind : ∀ m : ℕ, J.restrictScalars P ≤ J₀.restrictScalars P ⊔ I ^ m • J.restrictScalars P
      := by
      intro m; induction m with
      | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
      | succ m ih =>
        calc J.restrictScalars P ≤ J₀.restrictScalars P ⊔ I ^ m • J.restrictScalars P := ih
          _ ≤ J₀.restrictScalars P ⊔ I ^ m • (J₀.restrictScalars P ⊔ I • J.restrictScalars P) :=
              sup_le_sup_left (Submodule.smul_mono le_rfl hJle) _
          _ = J₀.restrictScalars P ⊔ (I ^ m • J₀.restrictScalars P ⊔ I ^ (m + 1) •
            J.restrictScalars P) := by
              rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
          _ ≤ J₀.restrictScalars P ⊔ I ^ (m + 1) • J.restrictScalars P :=
              sup_le le_sup_left (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)
    have h := hind k
    rw [hk, Submodule.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at h
    intro j hj
    exact h hj
  refine ⟨⟨n, ψ, hψs, ?_⟩⟩
  change J.FG
  rw [hJeq]
  exact Submodule.fg_span (Set.finite_range lift)

end Algebra.FinitePresentation
