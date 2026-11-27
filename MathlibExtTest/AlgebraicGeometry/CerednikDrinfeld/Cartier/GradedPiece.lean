/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.GradedPiece

@[expose] public noncomputable section

namespace CartierGradedPieceTest

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Consumer with the original binders for membership in a graded piece. -/
theorem exactSource {B : Type u} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (n : ℕ) (f : CartierModule p X.F) :
    f ∈ X.gradedPiece j n ↔ ∀ c : GaloisField p 2,
      endAct (X.actEnd (WittVector.teichmuller p c)) f =
        homothety (j (WittVector.teichmuller p c) ^ p ^ n) f :=
  X.mem_gradedPiece_iff j n f

/-- Consumer with the original binders: the grading has period two. -/
theorem exactSourcePeriodic {B : Type u} [CommRing B] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (n k : ℕ) : X.gradedPiece j (n + 2 * k) = X.gradedPiece j n :=
  X.gradedPiece_add_two_mul j n k

/-- The field with `p ^ 2` elements has an element that Frobenius moves. -/
theorem exists_pow_ne_self : ∃ c : GaloisField p 2, c ^ p ≠ c := by
  by_contra! h
  have h1 : FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p 2) = 1 := by
    ext c
    rw [FiniteField.frobeniusAlgHom_apply, ZMod.card, AlgHom.one_apply, h c]
  have h2 := FiniteField.orderOf_frobeniusAlgHom (ZMod p) (GaloisField p 2)
  rw [h1, orderOf_one, GaloisField.finrank p two_ne_zero] at h2
  exact absurd h2 (by norm_num)

/-- On the tangent space of the standard special formal `O_D`-module, the Teichmüller
representative `[c]` acts by `j [c]` on the first coordinate and by `j [c] ^ p` on the second. -/
theorem tangent_endAct_actEnd_standard {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (c : GaloisField p 2) (f : CartierModule p (SpecialFormalODModule.standard j).F) (i : Fin 2) :
    tangent (endAct ((SpecialFormalODModule.standard j).actEnd (WittVector.teichmuller p c)) f) i =
      j (WittVector.teichmuller p c) ^ p ^ (i : ℕ) * tangent f i :=
  (congrFun (tangent_map ((SpecialFormalODModule.standard j).actEnd
    (WittVector.teichmuller p c)) f) i).trans (by
      change (Standard.modB j).lieAct (WittVector.teichmuller p c) (tangent f) i = _
      rw [Standard.lieAct_apply]
      fin_cases i
      · simp
      · show j (Standard.chi 1 (WittVector.teichmuller p c)) * tangent f 1 =
          j (WittVector.teichmuller p c) ^ p ^ ((1 : Fin 2) : ℕ) * tangent f 1
        rw [Standard.chi_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
          frobenius_def, map_pow, map_pow, Fin.val_one, pow_one])

/-- In the standard special formal `O_D`-module over a domain, if `j [c] ^ p ≠ j [c]` for some
`c`, the tangent vector of every element of the graded piece `0` vanishes in the second
coordinate. -/
theorem tangent_one_eq_zero_of_mem_gradedPiece_zero {B : Type} [CommRing B] [IsDomain B]
    [CharP B p] (j : Zp2 p →+* B) {c : GaloisField p 2}
    (hc : j (WittVector.teichmuller p c) ^ p ≠ j (WittVector.teichmuller p c))
    {f : CartierModule p (SpecialFormalODModule.standard j).F}
    (hf : f ∈ (SpecialFormalODModule.standard j).gradedPiece j 0) : tangent f 1 = 0 := by
  have h := congrArg (fun g => tangent g 1) (hf c)
  simp only [tangent_homothety, pow_zero, pow_one, Pi.smul_apply, smul_eq_mul] at h
  rw [tangent_endAct_actEnd_standard] at h
  have h0 : (j (WittVector.teichmuller p c) ^ p - j (WittVector.teichmuller p c)) * tangent f 1
      = 0 := by
    rw [sub_mul, ← h, Fin.val_one, pow_one, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

/-- Under the same hypotheses, the tangent vector of every element of the graded piece `1`
vanishes in the first coordinate. -/
theorem tangent_zero_eq_zero_of_mem_gradedPiece_one {B : Type} [CommRing B] [IsDomain B]
    [CharP B p] (j : Zp2 p →+* B) {c : GaloisField p 2}
    (hc : j (WittVector.teichmuller p c) ^ p ≠ j (WittVector.teichmuller p c))
    {f : CartierModule p (SpecialFormalODModule.standard j).F}
    (hf : f ∈ (SpecialFormalODModule.standard j).gradedPiece j 1) : tangent f 0 = 0 := by
  have h := congrArg (fun g => tangent g 0) (hf c)
  simp only [tangent_homothety, pow_one, Pi.smul_apply, smul_eq_mul] at h
  rw [tangent_endAct_actEnd_standard] at h
  have h0 : (j (WittVector.teichmuller p c) ^ p - j (WittVector.teichmuller p c)) * tangent f 0
      = 0 := by
    rw [sub_mul, ← h, Fin.val_zero, pow_zero, pow_one, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

/-- Over `GaloisField p 2`, with `j` the reduction of Witt vectors to their constant
coefficient, the graded pieces `0` and `1` of the standard special formal `O_D`-module meet
only in elements with zero tangent vector. -/
example (f : CartierModule p (SpecialFormalODModule.standard
      (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).F)
    (h0 : f ∈ (SpecialFormalODModule.standard
      (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).gradedPiece
        WittVector.constantCoeff 0)
    (h1 : f ∈ (SpecialFormalODModule.standard
      (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2)).gradedPiece
        WittVector.constantCoeff 1) : tangent f = 0 := by
  obtain ⟨c, hc⟩ := exists_pow_ne_self (p := p)
  have hc' : WittVector.constantCoeff (WittVector.teichmuller p c) ^ p ≠
      WittVector.constantCoeff (WittVector.teichmuller p c) := by
    rwa [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  funext i
  fin_cases i
  · exact tangent_zero_eq_zero_of_mem_gradedPiece_one _ hc' h1
  · exact tangent_one_eq_zero_of_mem_gradedPiece_zero _ hc' h0

end CartierGradedPieceTest
