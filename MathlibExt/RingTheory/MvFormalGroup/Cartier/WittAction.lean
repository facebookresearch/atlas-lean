/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_MvFormalGroup_CartierModuleWittAction.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Homothety

/-!
# The Witt-vector module structure on Cartier modules

Multiplication by a Witt vector `w` acts on Cartier modules by precomposition with the family
`WittLaw.mulFam w` of Witt multiplication polynomials. This gives
`CartierModule.instModuleWittVector`, a `WittVector p R`-module structure in which Teichmüller
representatives act by homotheties. Write `σ` for the Frobenius of the Witt vectors. Frobenius
is `σ`-semilinear (`frobenius_smul`); in characteristic `p`, Verschiebung satisfies
`w • V x = V (σ w • x)` (`smul_verschiebung`) and, over a perfect ring, is `σ⁻¹`-semilinear
(`verschiebung_smul`).

## References

* Th. Zink, *Cartiertheorie kommutativer formaler Gruppen*, Teubner-Texte zur Mathematik 68,
  Teubner, Leipzig, 1984.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open MvPolynomial in
theorem WittVector.teichmuller_mul_coeff (p : ℕ) [hp : Fact p.Prime] {A : Type u} [CommRing A]
    (a : A) (y : WittVector p A) (n : ℕ) :
    (WittVector.teichmuller p a * y).coeff n = a ^ p ^ n * y.coeff n := by
  let f : ∀ ⦃S : Type u⦄ [CommRing S], WittVector p S → WittVector p S → WittVector p S :=
    fun S _ x y => WittVector.teichmuller p (x.coeff 0) * y
  let g : ∀ ⦃S : Type u⦄ [CommRing S], WittVector p S → WittVector p S → WittVector p S :=
    fun S _ x y => WittVector.mk p fun n => x.coeff 0 ^ p ^ n * y.coeff n
  have hteich : WittVector.IsPoly p fun S _ (x : WittVector p S) =>
      WittVector.teichmuller p (x.coeff 0) := by
    refine ⟨⟨fun n => if n = 0 then X 0 else 0, ?_⟩⟩
    intro S _ x
    funext n
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n)]
  have hf : WittVector.IsPoly₂ p f :=
    @WittVector.IsPoly₂.comp p _ _ _ WittVector.mulIsPoly₂ hteich (WittVector.idIsPolyI' p)
  have hg : WittVector.IsPoly₂ p g := by
    refine ⟨⟨fun n => X ((0 : Fin 2), 0) ^ p ^ n * X ((1 : Fin 2), n), ?_⟩⟩
    intro S _ x y
    funext n
    simp [g, WittVector.peval, Function.uncurry]
  have key := WittVector.IsPoly₂.ext hf hg (fun S _ x y n => by
    simp only [f, g, map_mul, WittVector.ghostComponent_teichmuller]
    rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
      aeval_wittPolynomial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only
    rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hi']
    ring) A (WittVector.mk p fun n => if n = 0 then a else 0) y
  have h0 : (WittVector.mk p fun n => if n = 0 then a else (0 : A)).coeff 0 = a := by simp
  simp only [f, g, ↓reduceIte] at key
  rw [key, WittVector.coeff_mk]

namespace MvFormalGroup

open MvPowerSeries WittLaw

theorem _root_.WittVector.mk_coeff_eq {p : ℕ} {A : Type*} [CommRing A] (x : WittVector p A) :
    WittVector.mk p (fun m => x.coeff m) = x := by
  ext m; rfl

theorem _root_.WittVector.map_peval {k : ℕ} {A B : Type*} [CommRing A] [CommRing B]
    {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (φ : F) (Q : MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → ℕ → A) :
    φ (WittVector.peval Q x) = WittVector.peval Q fun i m => φ (x i m) := by
  unfold WittVector.peval
  let φ' : A →+* B := RingHomClass.toRingHom φ
  change φ' _ = _
  let ψ₁ : MvPolynomial (Fin k × ℕ) ℤ →+* B := φ'.comp
      (MvPolynomial.aeval (Function.uncurry x)).toRingHom
  let ψ₂ : MvPolynomial (Fin k × ℕ) ℤ →+* B :=
    (MvPolynomial.aeval (Function.uncurry fun i m => φ (x i m))).toRingHom
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp MvPolynomial.C) (ψ₂.comp MvPolynomial.C)) r
    · rcases im with ⟨i, m⟩
      simp [ψ₁, ψ₂, φ', Function.uncurry]
  exact RingHom.congr_fun hψ Q

theorem _root_.WittVector.peval_X {k : ℕ} (R : Type*) [CommRing R]
    (Q : MvPolynomial (Fin k × ℕ) ℤ) :
    WittVector.peval Q (fun i m => (MvPolynomial.X (i, m) : MvPolynomial (Fin k × ℕ) R)) =
      MvPolynomial.map (Int.castRingHom R) Q := by
  unfold WittVector.peval
  let ψ₁ : MvPolynomial (Fin k × ℕ) ℤ →+* MvPolynomial (Fin k × ℕ) R :=
    (MvPolynomial.aeval (Function.uncurry fun i m =>
      (MvPolynomial.X (i, m) : MvPolynomial (Fin k × ℕ) R))).toRingHom
  have hψ : ψ₁ = MvPolynomial.map (Int.castRingHom R) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp MvPolynomial.C)
        ((MvPolynomial.map (Int.castRingHom R)).comp MvPolynomial.C)) r
    · rcases im with ⟨i, m⟩
      simp [ψ₁, Function.uncurry]
  exact RingHom.congr_fun hψ Q

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

abbrev cVec {τ : Type*} (w : WittVector p R) : WittVector p (MvPolynomial τ R) :=
  WittVector.map (MvPolynomial.C : R →+* MvPolynomial τ R) w

def mulPoly (w : WittVector p R) (n : ℕ) : MvPolynomial ℕ R :=
  (cVec p w * WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)).coeff n

def mulFam (w : WittVector p R) : ℕ → MvPowerSeries ℕ R := fun n =>
    (mulPoly p w n : MvPowerSeries ℕ R)

variable {p}

@[simp] theorem mulFam_apply (w : WittVector p R) (n : ℕ) :
    mulFam p w n = (mulPoly p w n : MvPowerSeries ℕ R) := rfl

omit hp in
theorem coe_aeval {σ τ : Type*} (y : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    ((MvPolynomial.aeval y P : MvPolynomial τ R) : MvPowerSeries τ R) =
      subst (fun i => (y i : MvPowerSeries τ R)) (P : MvPowerSeries σ R) := by
  rw [subst_coe]
  let ψ₁ : MvPolynomial σ R →ₐ[R] MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.algHom R).comp (MvPolynomial.aeval y)
  let ψ₂ : MvPolynomial σ R →ₐ[R] MvPowerSeries τ R :=
    MvPolynomial.aeval fun i => (y i : MvPowerSeries τ R)
  have hψ : ψ₁ = ψ₂ := MvPolynomial.algHom_ext fun i => by simp [ψ₁, ψ₂]
  exact AlgHom.congr_fun hψ P

omit hp in
theorem coe_peval {k : ℕ} {τ : Type*} (Q : MvPolynomial (Fin k × ℕ) ℤ)
    (x : Fin k → ℕ → MvPolynomial τ R) :
    subst (fun im : Fin k × ℕ => (x im.1 im.2 : MvPowerSeries τ R))
      ((MvPolynomial.map (Int.castRingHom R) Q : MvPolynomial (Fin k × ℕ) R) :
        MvPowerSeries (Fin k × ℕ) R) =
      ((WittVector.peval Q x : MvPolynomial τ R) : MvPowerSeries τ R) := by
  rw [subst_coe]
  unfold WittVector.peval
  let ψ₁ : MvPolynomial (Fin k × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.aeval fun im : Fin k × ℕ => (x im.1 im.2 : MvPowerSeries τ R)).toRingHom.comp
      (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin k × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      (MvPolynomial.aeval (Function.uncurry x)).toRingHom
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp MvPolynomial.C) (ψ₂.comp MvPolynomial.C)) r
    · rcases im with ⟨i, m⟩
      simp [ψ₁, ψ₂, Function.uncurry]
  exact RingHom.congr_fun hψ Q

@[simp] theorem cVec_coeff {τ : Type*} (w : WittVector p R) (m : ℕ) :
    (cVec p (τ := τ) w).coeff m = MvPolynomial.C (w.coeff m) :=
  WittVector.map_coeff _ _ _

@[simp] theorem cVec_add {τ : Type*} (w₁ w₂ : WittVector p R) :
    cVec p (τ := τ) (w₁ + w₂) = cVec p w₁ + cVec p w₂ := map_add _ _ _

@[simp] theorem cVec_mul {τ : Type*} (w₁ w₂ : WittVector p R) :
    cVec p (τ := τ) (w₁ * w₂) = cVec p w₁ * cVec p w₂ := map_mul _ _ _

@[simp] theorem cVec_one {τ : Type*} : cVec p (τ := τ) (1 : WittVector p R) = 1 := map_one _

@[simp] theorem cVec_zero {τ : Type*} : cVec p (τ := τ) (0 : WittVector p R) = 0 := map_zero _

theorem mulPoly_eq_peval (w : WittVector p R) (n : ℕ) :
    mulPoly p w n = WittVector.peval (WittVector.wittMul p n)
      ![fun m => MvPolynomial.C (w.coeff m), MvPolynomial.X] := by
  rw [mulPoly, WittVector.mul_coeff]
  congr 1

theorem aeval_mulPoly {τ : Type*} (w : WittVector p R) (y : ℕ → MvPolynomial τ R) (n : ℕ) :
    MvPolynomial.aeval y (mulPoly p w n) = (cVec p w * WittVector.mk p y).coeff n := by
  rw [mulPoly, WittVector.mul_coeff, WittVector.mul_coeff,
    WittVector.map_peval (MvPolynomial.aeval y : MvPolynomial ℕ R →ₐ[R] MvPolynomial τ R)]
  congr 1
  funext i m
  fin_cases i
  · change MvPolynomial.aeval y ((cVec p (τ := ℕ) w).coeff m) = (cVec p (τ := τ) w).coeff m
    rw [cVec_coeff, cVec_coeff, MvPolynomial.aeval_C]
    rfl
  · change MvPolynomial.aeval y ((WittVector.mk p MvPolynomial.X).coeff m) =
      (WittVector.mk p y).coeff m
    rw [WittVector.coeff_mk, WittVector.coeff_mk, MvPolynomial.aeval_X]

theorem mulPoly_add (w₁ w₂ : WittVector p R) (n : ℕ) :
    mulPoly p (w₁ + w₂) n = WittVector.peval
        (WittVector.wittAdd p n) ![mulPoly p w₁, mulPoly p w₂] := by
  rw [mulPoly, cVec_add, add_mul, WittVector.add_coeff]
  rfl

theorem mulPoly_mul (w₁ w₂ : WittVector p R) (n : ℕ) :
    mulPoly p (w₁ * w₂) n = MvPolynomial.aeval (mulPoly p w₂) (mulPoly p w₁ n) := by
  rw [aeval_mulPoly, mulPoly, cVec_mul, mul_assoc]
  change _ = (cVec p w₁ * WittVector.mk p (fun m =>
    (cVec p w₂ * WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)).coeff m)).coeff n
  rw [WittVector.mk_coeff_eq]

theorem mulPoly_one (n : ℕ) : mulPoly p (1 : WittVector p R) n = MvPolynomial.X n := by
  rw [mulPoly, cVec_one, one_mul, WittVector.coeff_mk]

theorem mulPoly_zero (n : ℕ) : mulPoly p (0 : WittVector p R) n = 0 := by
  rw [mulPoly, cVec_zero, zero_mul, WittVector.zero_coeff]

theorem mulPoly_at_zero (w : WittVector p R) :
    mulPoly p w 0 = MvPolynomial.C (w.coeff 0) * MvPolynomial.X 0 := by
  rw [mulPoly, WittVector.mul_coeff_zero, cVec_coeff, WittVector.coeff_mk]

theorem mulPoly_teichmuller (a : R) (n : ℕ) :
    mulPoly p (WittVector.teichmuller p a) n = MvPolynomial.C (a ^ p ^ n) * MvPolynomial.X n := by
  rw [mulPoly, cVec, WittVector.map_teichmuller, WittVector.teichmuller_mul_coeff,
    WittVector.coeff_mk, map_pow]

def verPoly (R : Type u) [CommRing R] : ℕ → MvPolynomial ℕ R
  | 0 => 0
  | n + 1 => MvPolynomial.X n

omit hp in
@[simp] theorem verPoly_zero : verPoly R 0 = 0 := rfl

omit hp in
@[simp] theorem verPoly_succ (n : ℕ) : verPoly R (n + 1) = MvPolynomial.X n := rfl

omit hp in
theorem coe_verPoly (n : ℕ) : (verPoly R n : MvPowerSeries ℕ R) = verFam R n := by
  cases n with
  | zero => exact MvPolynomial.coe_zero
  | succ n => exact MvPolynomial.coe_X _

theorem frobenius_cVec {τ : Type} (w : WittVector p R) :
    WittVector.frobenius (cVec p (τ := τ) w) = cVec p (WittVector.frobenius w) :=
  (WittVector.IsPoly.map (WittVector.frobenius_isPoly p) _ w).symm

theorem aeval_verPoly_mulPoly (w : WittVector p R) (n : ℕ) :
    MvPolynomial.aeval (verPoly R) (mulPoly p w n) =
      Nat.casesOn n 0 fun k => mulPoly p (WittVector.frobenius w) k := by
  rw [aeval_mulPoly]
  have hV : WittVector.mk p (verPoly R) =
      WittVector.verschiebung (WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)) := by
    refine WittVector.ext fun m => ?_
    cases m with
    | zero => rw [WittVector.coeff_mk, WittVector.verschiebung_coeff_zero]; rfl
    | succ m =>
      rw [WittVector.coeff_mk, WittVector.verschiebung_coeff_succ, WittVector.coeff_mk]
      rfl
  rw [hV, mul_comm, ← WittVector.verschiebung_mul_frobenius, mul_comm, frobenius_cVec]
  cases n with
  | zero => exact WittVector.verschiebung_coeff_zero _
  | succ k => rw [WittVector.verschiebung_coeff_succ]; rfl

theorem mulPoly_pow_char [CharP R p] (w : WittVector p R) (n : ℕ) :
    mulPoly p w n ^ p =
      MvPolynomial.aeval (fun m => (MvPolynomial.X m : MvPolynomial ℕ R) ^ p)
        (mulPoly p (WittVector.frobenius w) n) := by
  rw [aeval_mulPoly, mulPoly, ← WittVector.coeff_frobenius_charP, map_mul, frobenius_cVec]
  congr 2
  refine WittVector.ext fun m => ?_
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk, WittVector.coeff_mk]

omit hp in
theorem isWeightedHomogeneous_peval_C_X {N : ℕ} {Q : MvPolynomial (Fin 2 × ℕ) ℤ}
    (hQ : MvPolynomial.IsWeightedHomogeneous (weight p ![0, 1]) Q N) (c : ℕ → R) :
    MvPolynomial.IsWeightedHomogeneous (fun m => p ^ m)
      (WittVector.peval Q ![fun m => MvPolynomial.C (c m), (MvPolynomial.X : ℕ → MvPolynomial ℕ R)])
      N := by
  classical
  unfold WittVector.peval
  set g : Fin 2 × ℕ → MvPolynomial ℕ R :=
    Function.uncurry ![fun m => MvPolynomial.C (c m), (MvPolynomial.X : ℕ → MvPolynomial ℕ R)]
    with hg
  rw [MvPolynomial.as_sum Q, map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
  have hwe : Finsupp.weight (weight p ![0, 1]) e = N := hQ (MvPolynomial.mem_support_iff.mp he)
  rw [MvPolynomial.aeval_monomial, eq_intCast, ← map_intCast (MvPolynomial.C (σ := ℕ) (R := R))]
  have hprod : MvPolynomial.IsWeightedHomogeneous (fun m => p ^ m)
      (e.prod fun im k => g im ^ k) N := by
    rw [Finsupp.prod, ← hwe, Finsupp.weight_apply, Finsupp.sum]
    refine MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun im _ => ?_
    rcases im with ⟨i, m⟩
    fin_cases i
    · have h := (MvPolynomial.isWeightedHomogeneous_C (fun m => p ^ m) (c m)).pow (e (0, m))
      simp only [smul_zero] at h
      simpa [g, weight] using h
    · have h := (MvPolynomial.isWeightedHomogeneous_X (R := R) (fun m => p ^ m) m).pow (e (1, m))
      simpa [g, weight, smul_eq_mul, mul_comm] using h
  have := (MvPolynomial.isWeightedHomogeneous_C (fun m => p ^ m)
    ((Q.coeff e : ℤ) : R)).mul hprod
  rwa [zero_add] at this

theorem isWeightedHomogeneous_mulPoly (w : WittVector p R) (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun m => p ^ m) (mulPoly p w n) (p ^ n) := by
  rw [mulPoly_eq_peval]
  exact isWeightedHomogeneous_peval_C_X (isWeightedHomogeneous_wittMul p n) _

theorem weight_eq_of_coeff_mulFam_ne_zero (w : WittVector p R) {n : ℕ} {e : ℕ →₀ ℕ}
    (h : coeff e (mulFam p w n) ≠ 0) : Finsupp.weight (fun m => p ^ m) e = p ^ n := by
  rw [mulFam_apply, MvPolynomial.coeff_coe] at h
  exact isWeightedHomogeneous_mulPoly w n h

theorem constantCoeff_mulFam (w : WittVector p R) (n : ℕ) : (mulFam p w n).constantCoeff = 0 := by
  by_contra h
  have h' : coeff (0 : ℕ →₀ ℕ) (mulFam p w n) ≠ 0 := by
    rwa [coeff_zero_eq_constantCoeff_apply]
  have hw := weight_eq_of_coeff_mulFam_ne_zero w h'
  rw [map_zero] at hw
  exact absurd hw.symm (pow_ne_zero n hp.out.ne_zero)

theorem constantCoeff_mulPoly (w : WittVector p R) (n : ℕ) :
    MvPolynomial.constantCoeff (mulPoly p w n) = 0 := by
  have h := constantCoeff_mulFam w n
  rwa [mulFam_apply, ← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    ← MvPolynomial.constantCoeff_eq] at h

theorem hasSubst_mulFam (w : WittVector p R) : HasSubst (mulFam p w) := by
  refine ⟨fun n => by rw [constantCoeff_mulFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun m => p ^ m) e)).subset fun n hn => ?_
  have hw := weight_eq_of_coeff_mulFam_ne_zero w hn
  change n < Finsupp.weight (fun m => p ^ m) e
  rw [hw]
  exact Nat.lt_pow_self hp.out.one_lt

def xVec (R : Type u) [CommRing R] (i : Fin 2) : WittVector p (MvPolynomial (Fin 2 × ℕ) R) :=
  WittVector.mk p fun m => MvPolynomial.X (i, m)

def addPolyR (R : Type u) [CommRing R] (m : ℕ) : MvPolynomial (Fin 2 × ℕ) R :=
  MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p m)

theorem coe_addPolyR (m : ℕ) :
    (addPolyR (p := p) R m : MvPowerSeries (Fin 2 × ℕ) R) = addFam p R m := rfl

omit hp in
@[simp] theorem xVec_coeff (i : Fin 2) (m : ℕ) :
    (xVec (p := p) R i).coeff m = MvPolynomial.X (i, m) := rfl

theorem xVec_add : xVec (p := p) R 0 + xVec R 1 = WittVector.mk p (addPolyR (p := p) R) := by
  refine WittVector.ext fun m => ?_
  rw [WittVector.add_coeff]
  change WittVector.peval
      (WittVector.wittAdd p m) ![(xVec (p := p) R 0).coeff, (xVec (p := p) R 1).coeff] =
    addPolyR (p := p) R m
  rw [addPolyR, ← WittVector.peval_X R (WittVector.wittAdd p m)]
  congr 1
  funext i k
  fin_cases i <;> rfl

theorem pairFam_mulFam (w : WittVector p R) :
    pairFam (mulFam p w) = fun im : Fin 2 × ℕ =>
      (((cVec p w * xVec R im.1).coeff im.2 : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  funext ⟨i, m⟩
  rw [pairFam_apply, mulFam_apply, xVec, ← aeval_mulPoly, coe_aeval]
  congr 1
  funext k
  exact (MvPolynomial.coe_X _).symm

theorem subst_addFam_mulFam (w : WittVector p R) (n : ℕ) :
    subst (addFam p R) (mulFam p w n) =
      (((cVec p w * (xVec R 0 + xVec R 1)).coeff n : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  have h : addFam p R = fun i => (addPolyR (p := p) R i : MvPowerSeries (Fin 2 × ℕ) R) := rfl
  rw [h, mulFam_apply, ← coe_aeval, aeval_mulPoly, xVec_add]

theorem isEndo_mulFam (w : WittVector p R) : IsEndo p (mulFam p w) := by
  refine ⟨hasSubst_mulFam w, constantCoeff_mulFam w, fun n => ?_⟩
  have hR : subst (pairFam (mulFam p w)) (addFam p R n) =
      (((cVec p w * xVec R 0 + cVec p w * xVec R 1).coeff n : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
    have key := coe_peval (R := R) (WittVector.wittAdd p n)
      (fun i m => (cVec p w * xVec (p := p) R i).coeff m)
    rw [WittVector.add_coeff, pairFam_mulFam, ← coe_addPolyR, addPolyR]
    refine key.trans ?_
    congr 2
    funext i
    fin_cases i <;> rfl
  rw [subst_addFam_mulFam, hR, mul_add]

theorem subst_mulFam_mulFam (w₁ w₂ : WittVector p R) (n : ℕ) :
    subst (mulFam p w₂) (mulFam p w₁ n) = mulFam p (w₁ * w₂) n := by
  rw [mulFam_apply, mulFam_apply, mulPoly_mul, coe_aeval]
  rfl

theorem mulFam_add (w₁ w₂ : WittVector p R) (n : ℕ) :
    mulFam p (w₁ + w₂) n = subst (fun im : Fin 2 × ℕ =>
      (Fin.cases (mulFam p w₁ im.2) (fun _ => mulFam p w₂ im.2) im.1 : MvPowerSeries ℕ R))
        (addFam p R n) := by
  have hfun : (fun im : Fin 2 × ℕ =>
      (Fin.cases (mulFam p w₁ im.2) (fun _ => mulFam p w₂ im.2) im.1 : MvPowerSeries ℕ R)) =
      fun im : Fin 2 × ℕ => ((![mulPoly p w₁, mulPoly p w₂] im.1 im.2 : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
    funext ⟨i, m⟩
    fin_cases i <;> rfl
  rw [hfun, addFam, coe_peval, mulFam_apply, mulPoly_add]

theorem mulFam_one : mulFam p (1 : WittVector p R) = fun n => X n := by
  funext n
  rw [mulFam_apply, mulPoly_one, MvPolynomial.coe_X]

theorem mulFam_zero : mulFam p (0 : WittVector p R) = fun _ => 0 := by
  funext n
  rw [mulFam_apply, mulPoly_zero, MvPolynomial.coe_zero]

theorem mulFam_teichmuller (a : R) : mulFam p (WittVector.teichmuller p a) = teichFam p a := by
  funext n
  rw [mulFam_apply, mulPoly_teichmuller, MvPolynomial.coe_mul, MvPolynomial.coe_C,
    MvPolynomial.coe_X, teichFam_apply, smul_eq_C_mul]

theorem subst_verFam_mulFam (w : WittVector p R) (n : ℕ) :
    subst (verFam R) (mulFam p w n) =
      subst (mulFam p (WittVector.frobenius w)) (verFam R n) := by
  have hv : (verFam R) = fun m => (verPoly R m : MvPowerSeries ℕ R) := funext fun m =>
      (coe_verPoly m).symm
  rw [mulFam_apply, hv, ← coe_aeval, aeval_verPoly_mulPoly]
  cases n with
  | zero =>
    change ((0 : MvPolynomial ℕ R) : MvPowerSeries ℕ R) = subst _
        ((verPoly R 0 : MvPolynomial ℕ R) : MvPowerSeries ℕ R)
    rw [verPoly_zero, MvPolynomial.coe_zero, ← coe_substAlgHom (hasSubst_mulFam _), map_zero]
  | succ k =>
    change ((mulPoly p (WittVector.frobenius w) k : MvPolynomial ℕ R) : MvPowerSeries ℕ R) =
      subst _ ((verPoly R (k + 1) : MvPolynomial ℕ R) : MvPowerSeries ℕ R)
    rw [verPoly_succ, MvPolynomial.coe_X, subst_X (hasSubst_mulFam _), mulFam_apply]

theorem subst_mulFam_frobFam [CharP R p] (w : WittVector p R) (n : ℕ) :
    subst (mulFam p w) (frobFam p R n) =
      subst (frobFam p R) (mulFam p (WittVector.frobenius w) n) := by
  rw [frobFam_apply, subst_pow (hasSubst_mulFam w), subst_X (hasSubst_mulFam w), mulFam_apply,
    ← MvPolynomial.coe_pow, mulPoly_pow_char, coe_aeval, mulFam_apply]
  congr 1
  funext m
  rw [MvPolynomial.coe_pow, MvPolynomial.coe_X, frobFam_apply]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def wittSMul [Φ.IsComm] (w : WittVector p R) : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_mulFam w)

@[simp] theorem toPowerSeries_wittSMul [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    (wittSMul w f).toPowerSeries = fun j => subst (WittLaw.mulFam p w) (f.toPowerSeries j) := rfl

theorem wittSMul_one [Φ.IsComm] (f : CartierModule p Φ) : wittSMul (1 : WittVector p R) f = f := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_wittSMul, WittLaw.mulFam_one]
  exact congrFun subst_self _

theorem wittSMul_zero_left [Φ.IsComm] (f : CartierModule p Φ) :
    wittSMul (0 : WittVector p R) f = 0 := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_wittSMul, WittLaw.mulFam_zero]
  exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)

theorem wittSMul_mul [Φ.IsComm] (w₁ w₂ : WittVector p R) (f : CartierModule p Φ) :
    wittSMul (w₁ * w₂) f = wittSMul w₁ (wittSMul w₂ f) := by
  apply CartierModule.ext
  funext j
  change (precomp _ f).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, toPowerSeries_precomp]
  change subst (WittLaw.mulFam p (w₁ * w₂)) (f.toPowerSeries j) = _
  congr 1
  funext n
  rw [WittLaw.subst_mulFam_mulFam, mul_comm]

theorem wittSMul_add_left [Φ.IsComm] (w₁ w₂ : WittVector p R) (f : CartierModule p Φ) :
    wittSMul (w₁ + w₂) f = wittSMul w₁ f + wittSMul w₂ f := by
  apply CartierModule.ext
  funext j
  have hf := f.constantCoeff_eq_zero
  have hS : HasSubst (fun im : Fin 2 × ℕ => (Fin.cases (WittLaw.mulFam p w₁ im.2)
      (fun _ => WittLaw.mulFam p w₂ im.2) im.1 : MvPowerSeries ℕ R)) :=
    WittLaw.hasSubst_finCases (WittLaw.hasSubst_mulFam w₁) (WittLaw.hasSubst_mulFam w₂)
  have hfam : WittLaw.mulFam p (w₁ + w₂) = fun k => subst (fun im : Fin 2 × ℕ =>
      (Fin.cases (WittLaw.mulFam p w₁ im.2) (fun _ => WittLaw.mulFam p w₂ im.2) im.1 :
        MvPowerSeries ℕ R)) (WittLaw.addFam p R k) :=
    funext (WittLaw.mulFam_add w₁ w₂)
  rw [toPowerSeries_wittSMul, toPowerSeries_add]
  change subst (WittLaw.mulFam p (w₁ + w₂)) (f.toPowerSeries j) = _
  rw [hfam, ← subst_comp_subst_apply (hasSubst_addFam p R) hS, f.subst_addFam,
    subst_subst_elim Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hS]
  congr 1
  funext s
  rcases s with l | l
  · change subst _ (subst (blk 0) (f.toPowerSeries l)) = (wittSMul w₁ f).toPowerSeries l
    rw [subst_comp_subst_apply (hasSubst_blk 0) hS]
    congr 1
    funext m
    exact subst_X hS ((0 : Fin 2), m)
  · change subst _ (subst (blk 1) (f.toPowerSeries l)) = (wittSMul w₂ f).toPowerSeries l
    rw [subst_comp_subst_apply (hasSubst_blk 1) hS]
    congr 1
    funext m
    exact subst_X hS ((1 : Fin 2), m)

/-- For a commutative formal group law `Φ`, a Witt vector `w` acts on the Cartier module by
precomposition with Witt vector multiplication by `w`; this makes the Cartier module a
`WittVector p R`-module. -/
instance instModuleWittVector [Φ.IsComm] : Module (WittVector p R) (CartierModule p Φ) where
  smul w f := wittSMul w f
  one_smul := wittSMul_one
  mul_smul := wittSMul_mul
  smul_zero w := map_zero (wittSMul w)
  smul_add w := map_add (wittSMul w)
  add_smul := wittSMul_add_left
  zero_smul := wittSMul_zero_left

theorem smul_def [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) : w • f = wittSMul w f :=
    rfl

theorem smul_eq_precomp [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    w • f = precomp (WittLaw.isEndo_mulFam w) f := rfl

@[simp] theorem toPowerSeries_smul_witt [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    (w • f).toPowerSeries = fun j => subst (WittLaw.mulFam p w) (f.toPowerSeries j) := rfl

theorem teichmuller_smul [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    WittVector.teichmuller p a • f = homothety a f := by
  apply CartierModule.ext
  funext j
  rw [toPowerSeries_smul_witt, toPowerSeries_homothety, WittLaw.mulFam_teichmuller]

theorem homothety_smul_witt [Φ.IsComm] (a : R) (w : WittVector p R) (f : CartierModule p Φ) :
    homothety a (w • f) = w • homothety a f := by
  rw [← teichmuller_smul, ← teichmuller_smul, smul_smul, smul_smul, mul_comm]

theorem natCast_smul_eq_nsmul' [Φ.IsComm] (n : ℕ) (f : CartierModule p Φ) :
    (n : WittVector p R) • f = n • f :=
  Nat.cast_smul_eq_nsmul _ n f

theorem frobenius_smul [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    frobenius (w • f) = WittVector.frobenius w • frobenius f := by
  apply CartierModule.ext
  funext j
  change (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact WittLaw.subst_verFam_mulFam w n

theorem smul_verschiebung [Φ.IsComm] [CharP R p] (w : WittVector p R) (f : CartierModule p Φ) :
    w • verschiebung f = verschiebung (WittVector.frobenius w • f) := by
  apply CartierModule.ext
  funext j
  change (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact WittLaw.subst_mulFam_frobFam w n

theorem verschiebung_smul [Φ.IsComm] [CharP R p] [PerfectRing R p] (w : WittVector p R)
    (f : CartierModule p Φ) :
    verschiebung (w • f) = (WittVector.frobeniusEquiv p R).symm w • verschiebung f := by
  have hw : WittVector.frobenius ((WittVector.frobeniusEquiv p R).symm w) = w := by
    rw [← WittVector.frobeniusEquiv_apply]
    exact (WittVector.frobeniusEquiv p R).apply_symm_apply w
  rw [smul_verschiebung, hw]

theorem verschiebung_frobenius_eq_smul [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    verschiebung (frobenius f) = (p : WittVector p R) • f := by
  rw [verschiebung_frobenius, natCast_smul_eq_nsmul']

theorem map_smul_witt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (w : WittVector p R)
    (f : CartierModule p Φ) : map φ (w • f) = w • map φ f :=
  map_precomp φ _ f

theorem endAct_smul_witt [Φ.IsComm] (φ : MvFormalGroup.End Φ) (w : WittVector p R)
    (f : CartierModule p Φ) : endAct φ (w • f) = w • endAct φ f :=
  map_precomp φ _ f

def mapLinear [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') :
    CartierModule p Φ →ₗ[WittVector p R] CartierModule p Φ' :=
  { map φ with map_smul' := fun w f => map_smul_witt φ w f }

@[simp] theorem mapLinear_apply [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    mapLinear φ f = map φ f := rfl

theorem coeff_single_zero_subst_of_weight {u : ℕ → MvPowerSeries ℕ R}
    (hu : ∀ n (e : ℕ →₀ ℕ), coeff e (u n) ≠ 0 → Finsupp.weight (fun m => p ^ m) e = p ^ n)
    (g : MvPowerSeries ℕ R) (hg : g.constantCoeff = 0) :
    coeff (Finsupp.single 0 1) (subst u g) =
      coeff (Finsupp.single 0 1) g * coeff (Finsupp.single 0 1) (u 0) := by
  classical
  have hu0 : ∀ n, (u n).constantCoeff = 0 := by
    intro n
    by_contra h
    have h' : coeff (0 : ℕ →₀ ℕ) (u n) ≠ 0 := by rwa [coeff_zero_eq_constantCoeff_apply]
    have hw := hu n 0 h'
    rw [map_zero] at hw
    exact absurd hw.symm (pow_ne_zero n hp.out.ne_zero)
  have hus : HasSubst u := by
    refine ⟨fun n => by rw [hu0]; exact IsNilpotent.zero, fun e => ?_⟩
    refine (Set.finite_lt_nat (Finsupp.weight (fun m => p ^ m) e)).subset fun n hn => ?_
    have hw := hu n e hn
    change n < Finsupp.weight (fun m => p ^ m) e
    rw [hw]
    exact Nat.lt_pow_self hp.out.one_lt
  have hord : ∀ n, ((p ^ n : ℕ) : ℕ∞) ≤ (u n).weightedOrder (fun m => p ^ m) := by
    intro n
    refine nat_le_weightedOrder (fun m => p ^ m) fun e he => ?_
    by_contra hne
    have hw := hu n e hne
    rw [hw] at he
    exact lt_irrefl _ he
  rw [coeff_subst hus]
  have hterm : ∀ e : ℕ →₀ ℕ, e ≠ Finsupp.single 0 1 →
      coeff e g • coeff (Finsupp.single 0 1) (e.prod fun n k => u n ^ k) = 0 := by
    intro e he
    by_cases he0 : e = 0
    · subst he0
      rw [coeff_zero_eq_constantCoeff_apply, hg, zero_smul]
    · have hwt : (2 : ℕ∞) ≤ (e.prod fun n k => u n ^ k).weightedOrder (fun m => p ^ m) := by
        rw [Finsupp.prod]
        refine le_trans ?_ (le_weightedOrder_prod _ _ _)
        have hle : ∀ n ∈ e.support, ((e n * p ^ n : ℕ) : ℕ∞) ≤
            (u n ^ e n).weightedOrder (fun m => p ^ m) := by
          intro n _
          refine le_trans ?_ (le_weightedOrder_pow _ _)
          rw [Nat.cast_mul]
          calc ((e n : ℕ) : ℕ∞) * ((p ^ n : ℕ) : ℕ∞) = (e n) • ((p ^ n : ℕ) : ℕ∞) := by
                rw [nsmul_eq_mul]
            _ ≤ (e n) • (u n).weightedOrder (fun m => p ^ m) := nsmul_le_nsmul_right (hord n) _
        refine le_trans ?_ (Finset.sum_le_sum hle)
        rw [← Nat.cast_sum]
        have h2 : 2 ≤ ∑ n ∈ e.support, e n * p ^ n := by
          by_cases hsupp : ∃ n ∈ e.support, n ≠ 0
          · obtain ⟨n, hn, hn0⟩ := hsupp
            refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn)
            have hen : 1 ≤ e n := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hn)
            have hpn : 2 ≤ p ^ n := le_trans hp.out.two_le
              (Nat.le_self_pow hn0 p)
            calc 2 ≤ 1 * p ^ n := by omega
              _ ≤ e n * p ^ n := Nat.mul_le_mul_right _ hen
          · push Not at hsupp
            have hes : e = Finsupp.single 0 (e 0) := by
              ext n
              by_cases hn : n = 0
              · subst hn; simp
              · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hn)]
                by_contra hne
                exact hn (hsupp n (Finsupp.mem_support_iff.mpr hne))
            have hk0 : e 0 ≠ 0 := fun h => he0 (by rw [hes, h, Finsupp.single_zero])
            have hk1 : e 0 ≠ 1 := fun h => he (by rw [hes, h])
            have hk : 2 ≤ e 0 := by omega
            have h0 : (0 : ℕ) ∈ e.support := Finsupp.mem_support_iff.mpr (by omega)
            refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) h0)
            simpa using hk
        exact_mod_cast h2
      have hzero : coeff (Finsupp.single 0 1) (e.prod fun n k => u n ^ k) = 0 := by
        refine coeff_eq_zero_of_lt_weightedOrder (fun m => p ^ m) (lt_of_lt_of_le ?_ hwt)
        rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
        simp
      rw [hzero, smul_zero]
  rw [finsum_eq_single _ (Finsupp.single 0 1) hterm, Finsupp.prod_single_index (by simp), pow_one,
    smul_eq_mul]

theorem tangent_smul_witt [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    tangent (w • f) = w.coeff 0 • tangent f := by
  classical
  funext j
  rw [tangent_apply, toPowerSeries_smul_witt, Pi.smul_apply, tangent_apply, smul_eq_mul]
  change coeff (Finsupp.single 0 1) (subst (WittLaw.mulFam p w) (f.toPowerSeries j)) = _
  rw [coeff_single_zero_subst_of_weight (fun n e h => WittLaw.weight_eq_of_coeff_mulFam_ne_zero w h)
    _ (f.constantCoeff_eq_zero j), WittLaw.mulFam_apply, WittLaw.mulPoly_at_zero,
    MvPolynomial.coeff_coe, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_same, mul_one, mul_comm]

namespace Examples

theorem smul_addLinear (w : WittVector p R) (v : Fin d → R) :
    w • addLinear p v = addLinear p (w.coeff 0 • v) := by
  apply CartierModule.ext
  funext i
  rw [toPowerSeries_smul_witt, toPowerSeries_addLinear]
  change subst (WittLaw.mulFam p w) ((addLinear p v).toPowerSeries i) = _
  rw [toPowerSeries_addLinear, subst_smul (WittLaw.hasSubst_mulFam w),
    subst_X (WittLaw.hasSubst_mulFam w), WittLaw.mulFam_apply, WittLaw.mulPoly_at_zero,
    MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X, Pi.smul_apply, smul_eq_mul,
    ← smul_eq_C_mul, smul_smul, mul_comm]

end Examples

end CartierModule

end MvFormalGroup

end
