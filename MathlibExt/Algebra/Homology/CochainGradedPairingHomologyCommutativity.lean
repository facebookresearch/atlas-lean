/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws

/-!
# Scalar commutation identities for cochain pairings on homology

Let `K` be a natural-index cochain complex over a commutative ring and `P`, `Q` two graded
pairings on it. Fix degrees `p`, `q` and an integer `z`. Suppose the chain-level pairings
satisfy `P(x,y) = z • Q(y,x)` after transport from degree `p + q` to degree `q + p`.

The same identity holds on all homology classes, as an equality of elements in the graded
family `n ↦ K.homology n`. The scalar `z` is arbitrary, so the statement includes any
specified commutation sign.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace HomologicalComplex.CochainGradedPairing

variable (R : Type u) [CommRing R]

private noncomputable def commCyclesTransportAddHom
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q) :
    K.cycles p →+ K.cycles q where
  toFun x := cast (congrArg (fun n => ↥(K.cycles n)) h) x
  map_zero' := by subst h; rfl
  map_add' x y := by subst h; rfl

private noncomputable def commHomologyTransportAddHom
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q) :
    K.homology p →+ K.homology q where
  toFun x := cast (congrArg (fun n => ↥(K.homology n)) h) x
  map_zero' := by subst h; rfl
  map_add' x y := by subst h; rfl

private lemma comm_homologyπ_transport
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q)
    (x : K.cycles p) :
    (commHomologyTransportAddHom R (K := K) h) ((K.homologyπ p).hom x) =
      (K.homologyπ q).hom ((commCyclesTransportAddHom R h) x) := by
  cases h
  rfl

private lemma comm_iCycles_transport
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q)
    (x : K.cycles p) :
    (K.iCycles q).hom ((commCyclesTransportAddHom R (K := K) h) x) =
      (K.XIsoOfEq h).hom.hom ((K.iCycles p).hom x) := by
  subst h
  simp [commCyclesTransportAddHom]

/-- Scalar commutation of chain pairings descends to graded homology.

For pairings `P` and `Q`, degrees `p`, `q`, and `z : ℤ`, assume the chain pairing values
satisfy the stated degree-transported scalar commutation identity on every pair of chain
terms. Then the degree-`p + q` class of `P.pairHomology(x,y)` equals `z` times the degree-`q +
p` class of `Q.pairHomology(y,x)` for all homology classes `x` and `y`. -/
theorem pairHomology_comm_mk_of_pair
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    (P Q : CochainGradedPairing K K K) (z : ℤ)
    (p q : ℕ)
    (hpair : ∀ (x : K.X p) (y : K.X q),
      (K.XIsoOfEq (Nat.add_comm p q)).hom.hom
          ((P.pair p q).hom (x ⊗ₜ[R] y)) =
        z • (Q.pair q p).hom (y ⊗ₜ[R] x))
    (x : K.homology p) (y : K.homology q) :
    (GradedMonoid.mk (p + q)
        ((P.pairHomology p q).hom (x ⊗ₜ[R] y)) :
      GradedMonoid (fun n ↦ K.homology n)) =
      z • GradedMonoid.mk (q + p)
        ((Q.pairHomology q p).hom (y ⊗ₜ[R] x)) := by
  obtain ⟨x₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ p)).mp inferInstance x
  obtain ⟨y₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance y
  have h_eq : p + q = q + p := Nat.add_comm p q
  have h_left :
      (P.pairHomology p q).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀) =
        (K.homologyπ (p + q)).hom ((P.pairCycles p q).hom (x₀ ⊗ₜ[R] y₀)) :=
    pairHomology_π_apply R P p q x₀ y₀
  have h_right :
      (Q.pairHomology q p).hom
          ((K.homologyπ q).hom y₀ ⊗ₜ[R] (K.homologyπ p).hom x₀) =
        (K.homologyπ (q + p)).hom ((Q.pairCycles q p).hom (y₀ ⊗ₜ[R] x₀)) :=
    pairHomology_π_apply R Q q p y₀ x₀
  have h_cyc :
      (commCyclesTransportAddHom R h_eq)
          ((P.pairCycles p q).hom (x₀ ⊗ₜ[R] y₀)) =
        z • (Q.pairCycles q p).hom (y₀ ⊗ₜ[R] x₀) := by
    apply (ModuleCat.mono_iff_injective (f := K.iCycles (q + p))).mp inferInstance
    rw [comm_iCycles_transport R h_eq]
    simp only [pairCycles_i_apply R, map_zsmul]
    exact hpair ((K.iCycles p).hom x₀) ((K.iCycles q).hom y₀)
  have h_hom :
      (commHomologyTransportAddHom R h_eq)
          ((P.pairHomology p q).hom
            ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀)) =
        z • (Q.pairHomology q p).hom
          ((K.homologyπ q).hom y₀ ⊗ₜ[R] (K.homologyπ p).hom x₀) := by
    rw [h_left, comm_homologyπ_transport R h_eq, h_cyc, map_zsmul, h_right]
  have h_heq : HEq
      ((P.pairHomology p q).hom
        ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀))
      (z • (Q.pairHomology q p).hom
        ((K.homologyπ q).hom y₀ ⊗ₜ[R] (K.homologyπ p).hom x₀)) := by
    have ht : HEq
        ((P.pairHomology p q).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀))
        ((commHomologyTransportAddHom R h_eq)
          ((P.pairHomology p q).hom
            ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀))) :=
      (cast_heq (congrArg (fun n => ↥(K.homology n)) h_eq)
        ((P.pairHomology p q).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀))).symm
    exact HEq.trans ht (heq_of_eq h_hom)
  exact Sigma.ext h_eq h_heq

end HomologicalComplex.CochainGradedPairing
