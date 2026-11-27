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
`Definitions/Def_MvFormalGroup_CartierModuleIntVerschiebung.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.WittAction

/-!
# The Verschiebung defined over any base

`CartierModule.verschiebungInt` precomposes with the Witt Frobenius polynomials and needs no
characteristic hypothesis. In characteristic `p` it agrees with `CartierModule.verschiebung`
(`verschiebungInt_eq_verschiebung`), and in general `frobenius ∘ verschiebungInt` is
multiplication by `p` (`frobenius_verschiebungInt`).

## References

* Th. Zink, *Cartiertheorie kommutativer formaler Gruppen*, Teubner-Texte zur Mathematik 68,
  Teubner, Leipzig, 1984.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace WittVector

open MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

theorem teichmuller_coeff_zero_isPoly :
    WittVector.IsPoly p fun (S : Type u) (_ : CommRing S) (x : WittVector p S) =>
      WittVector.teichmuller p (x.coeff 0) := by
  refine ⟨⟨fun n => if n = 0 then X 0 else 0, ?_⟩⟩
  intro S _ x
  funext n
  cases n with
  | zero => simp [WittVector.teichmuller_coeff_zero]
  | succ n => simp [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n)]

theorem teichmuller_coeff_zero_pow_isPoly :
    WittVector.IsPoly p fun (S : Type u) (_ : CommRing S) (x : WittVector p S) =>
      WittVector.teichmuller p (x.coeff 0 ^ p) := by
  refine ⟨⟨fun n => if n = 0 then X 0 ^ p else 0, ?_⟩⟩
  intro S _ x
  funext n
  cases n with
  | zero =>
    rw [WittVector.teichmuller_coeff_zero]
    simp
  | succ n =>
    rw [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n)]
    simp

theorem frobenius_teichmuller_eq {A : Type u} [CommRing A] (a : A) :
    WittVector.frobenius (WittVector.teichmuller p a) = WittVector.teichmuller p (a ^ p) := by
  have hf : WittVector.IsPoly p fun (S : Type u) (_ : CommRing S) (x : WittVector p S) =>
      WittVector.frobenius (WittVector.teichmuller p (x.coeff 0)) :=
    @WittVector.IsPoly.comp p _ _ (WittVector.frobenius_isPoly p) (teichmuller_coeff_zero_isPoly p)
  have key := WittVector.IsPoly.ext hf (teichmuller_coeff_zero_pow_isPoly p) (fun S _ x n => by
    simp only [WittVector.ghostComponent_frobenius, WittVector.ghostComponent_teichmuller]
    rw [← pow_mul, ← pow_succ']) A (WittVector.teichmuller p a)
  simpa only [WittVector.teichmuller_coeff_zero] using key

theorem isWeightedHomogeneous_frobeniusPoly (n : ℕ) :
    IsWeightedHomogeneous (fun m : ℕ => p ^ m) (WittVector.frobeniusPoly p n) (p ^ (n + 1)) := by
  have hW : ∀ N : ℕ, IsWeightedHomogeneous (fun m : ℕ => p ^ m) (wittPolynomial p ℤ N) (p ^ N) := by
    intro N
    rw [wittPolynomial_eq_sum_C_mul_X_pow]
    refine IsWeightedHomogeneous.sum _ _ _ fun j hj => ?_
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hX := (isWeightedHomogeneous_X (R := ℤ) (fun m : ℕ => p ^ m) j).pow (p ^ (N - j))
    have hdeg : (p ^ (N - j)) • (fun m : ℕ => p ^ m) j = p ^ N := by
      change p ^ (N - j) * p ^ j = p ^ N
      rw [← pow_add, Nat.sub_add_cancel hj']
    rw [hdeg] at hX
    exact hX.C_mul _
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key := WittVector.bind₁_frobeniusPoly_wittPolynomial p n
    rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      pow_one] at key
    simp only [map_mul, MvPolynomial.bind₁_C_right, map_pow, MvPolynomial.bind₁_X_right] at key
    have hsum : IsWeightedHomogeneous (fun m : ℕ => p ^ m)
        (∑ i ∈ Finset.range n, C (p : ℤ) ^ i * WittVector.frobeniusPoly p i ^ p ^ (n - i))
          (p ^ (n + 1)) := by
      refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have h1 := (ih i hi').pow (p ^ (n - i))
      have hdeg : (p ^ (n - i)) • p ^ (i + 1) = p ^ (n + 1) := by
        rw [smul_eq_mul, ← pow_add]
        congr 1
        omega
      rw [hdeg] at h1
      rw [← map_pow]
      exact h1.C_mul _
    intro d hd
    by_contra hne
    have hcoeff : (C (p : ℤ) ^ n * WittVector.frobeniusPoly p n).coeff d = 0 := by
      have := congrArg (fun q => q.coeff d) key
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at this
      have hR : (wittPolynomial p ℤ (n + 1)).coeff d = 0 :=
        (hW (n + 1)).coeff_eq_zero d hne
      have hS : (∑ i ∈ Finset.range n,
          C (p : ℤ) ^ i * WittVector.frobeniusPoly p i ^ p ^ (n - i)).coeff d = 0 :=
        hsum.coeff_eq_zero d hne
      rw [hR, hS, zero_add] at this
      exact this
    rw [← map_pow, MvPolynomial.coeff_C_mul] at hcoeff
    rcases mul_eq_zero.mp hcoeff with h | h
    · exact absurd h (pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.out.ne_zero))
    · exact hd h

end WittVector

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R]

def xTaut : WittVector p (MvPolynomial ℕ R) :=
  WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)

def frobPoly (n : ℕ) : MvPolynomial ℕ R := (WittVector.frobenius (xTaut p R)).coeff n

def frobPolyFam : ℕ → MvPowerSeries ℕ R := fun n => (frobPoly p R n : MvPowerSeries ℕ R)

variable {p R}

omit hp in
@[simp] theorem xTaut_coeff (m : ℕ) : (xTaut p R).coeff m = MvPolynomial.X m := rfl

@[simp] theorem frobPolyFam_apply (n : ℕ) : frobPolyFam p R n =
    (frobPoly p R n : MvPowerSeries ℕ R) :=
  rfl

theorem aeval_X_intCast {σ : Type*} (S : Type*) [CommRing S] (φ : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S) φ =
      MvPolynomial.map (Int.castRingHom S) φ := by
  refine RingHom.congr_fun (?_ :
    (MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom =
      MvPolynomial.map (Int.castRingHom S)) φ
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_int
      ((MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom.comp
        (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))
      ((MvPolynomial.map (Int.castRingHom S)).comp (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))) r
  · simp

theorem frobPoly_eq_map (n : ℕ) :
    frobPoly p R n = MvPolynomial.map (Int.castRingHom R) (WittVector.frobeniusPoly p n) := by
  rw [frobPoly, WittVector.coeff_frobenius, ← aeval_X_intCast]
  rfl

theorem aeval_frobPoly {τ : Type} (y : ℕ → MvPolynomial τ R) (n : ℕ) :
    MvPolynomial.aeval y (frobPoly p R n) = (WittVector.frobenius (WittVector.mk p y)).coeff n := by
  have h := WittVector.IsPoly.map (WittVector.frobenius_isPoly p)
    (MvPolynomial.aeval y : MvPolynomial ℕ R →ₐ[R] MvPolynomial τ R).toRingHom (xTaut p R)
  have hx : WittVector.map
      (MvPolynomial.aeval y : MvPolynomial ℕ R →ₐ[R] MvPolynomial τ R).toRingHom
      (xTaut p R) = WittVector.mk p y := by
    refine WittVector.ext fun m => ?_
    rw [WittVector.map_coeff, xTaut_coeff, WittVector.coeff_mk]
    exact MvPolynomial.aeval_X y m
  rw [hx] at h
  rw [← h, WittVector.map_coeff]
  rfl

theorem frobPoly_charP [CharP R p] (n : ℕ) : frobPoly p R n = MvPolynomial.X n ^ p := by
  rw [frobPoly, WittVector.coeff_frobenius_charP, xTaut_coeff]

theorem frobPolyFam_eq_frobFam [CharP R p] : frobPolyFam p R = frobFam p R := by
  funext n
  rw [frobPolyFam_apply, frobPoly_charP, MvPolynomial.coe_pow, MvPolynomial.coe_X, frobFam_apply]

theorem isWeightedHomogeneous_frobPoly (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun m : ℕ => p ^ m) (frobPoly p R n) (p ^ (n + 1)) := by
  rw [frobPoly_eq_map]
  intro d hd
  rw [MvPolynomial.coeff_map] at hd
  have hd' : (WittVector.frobeniusPoly p n).coeff d ≠ 0 := fun h => hd (by rw [h, map_zero])
  exact WittVector.isWeightedHomogeneous_frobeniusPoly p n hd'

theorem weight_eq_of_coeff_frobPolyFam_ne_zero {n : ℕ} {e : ℕ →₀ ℕ}
    (h : coeff e (frobPolyFam p R n) ≠ 0) : Finsupp.weight (fun m : ℕ => p ^ m) e = p ^
        (n + 1) := by
  rw [frobPolyFam_apply, MvPolynomial.coeff_coe] at h
  exact isWeightedHomogeneous_frobPoly n h

theorem constantCoeff_frobPolyFam (n : ℕ) : (frobPolyFam p R n).constantCoeff = 0 := by
  by_contra h
  have h' : coeff (0 : ℕ →₀ ℕ) (frobPolyFam p R n) ≠ 0 := by
    rwa [coeff_zero_eq_constantCoeff_apply]
  have hw := weight_eq_of_coeff_frobPolyFam_ne_zero h'
  rw [map_zero] at hw
  exact absurd hw.symm (pow_ne_zero _ hp.out.ne_zero)

theorem constantCoeff_frobPoly (n : ℕ) : MvPolynomial.constantCoeff (frobPoly p R n) = 0 := by
  have h := constantCoeff_frobPolyFam (p := p) (R := R) n
  rwa [frobPolyFam_apply, ← coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    ← MvPolynomial.constantCoeff_eq] at h

theorem hasSubst_frobPolyFam : HasSubst (frobPolyFam p R) := by
  refine ⟨fun n => by rw [constantCoeff_frobPolyFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun m : ℕ => p ^ m) e)).subset fun n hn => ?_
  have hw := weight_eq_of_coeff_frobPolyFam_ne_zero hn
  change n < Finsupp.weight (fun m : ℕ => p ^ m) e
  rw [hw]
  exact (Nat.lt_pow_self hp.out.one_lt).trans (Nat.pow_lt_pow_right hp.out.one_lt n.lt_succ_self)

theorem pairFam_frobPolyFam :
    pairFam (frobPolyFam p R) = fun im : Fin 2 × ℕ =>
      (((WittVector.frobenius (xVec (p := p) R im.1)).coeff im.2 : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  funext ⟨i, m⟩
  rw [pairFam_apply, frobPolyFam_apply, xVec, ← aeval_frobPoly, coe_aeval]
  congr 1
  funext k
  exact (MvPolynomial.coe_X _).symm

theorem subst_addFam_frobPolyFam (n : ℕ) :
    subst (addFam p R) (frobPolyFam p R n) =
      (((WittVector.frobenius (xVec (p := p) R 0 + xVec R 1)).coeff n : MvPolynomial
          (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  have h : addFam p R = fun i => (addPolyR (p := p) R i : MvPowerSeries (Fin 2 × ℕ) R) := rfl
  rw [h, frobPolyFam_apply, ← coe_aeval, aeval_frobPoly, xVec_add]

theorem isEndo_frobPolyFam : IsEndo p (frobPolyFam p R) := by
  refine ⟨hasSubst_frobPolyFam, constantCoeff_frobPolyFam, fun n => ?_⟩
  have hR : subst (pairFam (frobPolyFam p R)) (addFam p R n) =
      (((WittVector.frobenius (xVec (p := p) R 0) + WittVector.frobenius
          (xVec (p := p) R 1)).coeff n :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    have key := coe_peval (R := R) (WittVector.wittAdd p n)
      (fun i m => (WittVector.frobenius (xVec (p := p) R i)).coeff m)
    rw [WittVector.add_coeff, pairFam_frobPolyFam, ← coe_addPolyR, addPolyR]
    refine key.trans ?_
    congr 2
    funext i
    fin_cases i <;> rfl
  rw [subst_addFam_frobPolyFam, hR, map_add]

theorem mk_frobPoly : WittVector.mk p (frobPoly p R) = WittVector.frobenius (xTaut p R) :=
  WittVector.mk_coeff_eq _

theorem subst_verFam_frobPolyFam (n : ℕ) :
    subst (verFam R) (frobPolyFam p R n) = nsmulFam p R p n := by
  have hv : (verFam R) = fun m => (verPoly R m : MvPowerSeries ℕ R) :=
    funext fun m => (coe_verPoly m).symm
  have hV : WittVector.mk p (verPoly R) = WittVector.verschiebung (xTaut p R) := by
    refine WittVector.ext fun m => ?_
    cases m with
    | zero => rw [WittVector.coeff_mk, WittVector.verschiebung_coeff_zero]; rfl
    | succ m => rw [WittVector.coeff_mk, WittVector.verschiebung_coeff_succ]; rfl
  rw [frobPolyFam_apply, hv, ← coe_aeval, aeval_frobPoly, hV, WittVector.frobenius_verschiebung,
    mul_comm, ← nsmul_eq_mul, WittVector.nsmul_coeff, nsmulFam]
  congr 1
  have hunc : Function.uncurry ![(xTaut p R).coeff] =
      fun im : Fin 1 × ℕ => (MvPolynomial.X im.2 : MvPolynomial ℕ R) := by
    funext ⟨i, m⟩
    fin_cases i; rfl
  change MvPolynomial.aeval (Function.uncurry ![(xTaut p R).coeff]) (WittVector.wittNSMul p p n) = _
  rw [hunc, show (fun im : Fin 1 × ℕ => (MvPolynomial.X im.2 : MvPolynomial ℕ R)) =
      (MvPolynomial.X : ℕ → MvPolynomial ℕ R) ∘ Prod.snd from rfl,
    ← MvPolynomial.aeval_rename, aeval_X_intCast]

theorem subst_mulFam_frobPolyFam (w : WittVector p R) (n : ℕ) :
    subst (mulFam p w) (frobPolyFam p R n) =
      subst (frobPolyFam p R) (mulFam p (WittVector.frobenius w) n) := by
  have hL : subst (mulFam p w) (frobPolyFam p R n) =
      (((WittVector.frobenius (cVec p w * xTaut p R)).coeff n : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
    have hm : mulFam p w = fun m => (mulPoly p w m : MvPowerSeries ℕ R) := rfl
    rw [hm, frobPolyFam_apply, ← coe_aeval, aeval_frobPoly]
    congr 3
  have hRt : subst (frobPolyFam p R) (mulFam p (WittVector.frobenius w) n) =
      (((cVec p (WittVector.frobenius w) * WittVector.frobenius (xTaut p R)).coeff n :
        MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
    have hf : frobPolyFam p R = fun m => (frobPoly p R m : MvPowerSeries ℕ R) := rfl
    rw [hf, mulFam_apply, ← coe_aeval, aeval_mulPoly, mk_frobPoly]
  rw [hL, hRt, map_mul, frobenius_cVec]

theorem subst_teichFam_frobPolyFam (a : R) (n : ℕ) :
    subst (teichFam p a) (frobPolyFam p R n) = subst (frobPolyFam p R) (teichFam p (a ^ p) n) := by
  rw [← mulFam_teichmuller, ← mulFam_teichmuller, ← WittVector.frobenius_teichmuller_eq]
  exact subst_mulFam_frobPolyFam _ n

def curvePoly (R : Type u) [CommRing R] : ℕ → MvPolynomial Unit R
  | 0 => MvPolynomial.X ()
  | _ + 1 => 0

omit hp in
theorem coe_curvePoly (n : ℕ) :
    ((curvePoly R n : MvPolynomial Unit R) : MvPowerSeries Unit R) =
        CartierModule.curveFam R n := by
  cases n with
  | zero => exact MvPolynomial.coe_X _
  | succ n => exact MvPolynomial.coe_zero

theorem mk_curvePoly :
    WittVector.mk p (curvePoly R) = WittVector.teichmuller p
        (MvPolynomial.X () : MvPolynomial Unit R) := by
  refine WittVector.ext fun m => ?_
  cases m with
  | zero => rw [WittVector.coeff_mk, WittVector.teichmuller_coeff_zero]; rfl
  | succ m =>
    rw [WittVector.coeff_mk, WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos m)]
    rfl

theorem subst_curveFam_frobPolyFam (n : ℕ) :
    subst (CartierModule.curveFam R) (frobPolyFam p R n) =
      Nat.casesOn n ((PowerSeries.X : PowerSeries R) ^ p) fun _ => 0 := by
  have hc : CartierModule.curveFam R = fun m => ((curvePoly R m : MvPolynomial Unit R) :
      MvPowerSeries Unit R) := funext fun m => (coe_curvePoly m).symm
  rw [hc, frobPolyFam_apply, ← coe_aeval, aeval_frobPoly, mk_curvePoly,
    WittVector.frobenius_teichmuller_eq]
  cases n with
  | zero =>
    rw [WittVector.teichmuller_coeff_zero, MvPolynomial.coe_pow, MvPolynomial.coe_X]
    rfl
  | succ m =>
    rw [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos m), MvPolynomial.coe_zero]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

/-- **Verschiebung over any base.** For a commutative formal group law `Φ` over any commutative
ring, `verschiebungInt` precomposes each point of the Cartier module with the Witt vector
Frobenius, given by the integral Frobenius polynomials of the Witt vectors. Over a ring of
characteristic `p` it agrees with `verschiebung`, and `F (verschiebungInt x) = p • x` over any
base. -/
def verschiebungInt [Φ.IsComm] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_frobPolyFam

theorem verschiebungInt_eq_precomp [Φ.IsComm] :
    (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ) =
        precomp WittLaw.isEndo_frobPolyFam :=
  rfl

@[simp] theorem toPowerSeries_verschiebungInt [Φ.IsComm] (f : CartierModule p Φ) :
    (verschiebungInt f).toPowerSeries = fun j => subst (WittLaw.frobPolyFam p R)
        (f.toPowerSeries j) :=
  rfl

theorem verschiebungInt_eq_verschiebung [Φ.IsComm] [CharP R p] :
    (verschiebungInt : CartierModule p Φ →+ CartierModule p Φ) = verschiebung := by
  refine AddMonoidHom.ext fun f => CartierModule.ext (funext fun j => ?_)
  rw [toPowerSeries_verschiebungInt, toPowerSeries_verschiebung, WittLaw.frobPolyFam_eq_frobFam]

theorem verschiebungInt_apply_eq_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    verschiebungInt f = verschiebung f := by
  rw [verschiebungInt_eq_verschiebung]

theorem frobenius_verschiebungInt [Φ.IsComm] (f : CartierModule p Φ) :
    frobenius (verschiebungInt f) = (p : ℕ) • f := by
  apply CartierModule.ext
  funext j
  rw [verschiebungInt, frobenius, precomp_precomp, ← subst_nsmulFam]
  congr 1
  funext k
  exact WittLaw.subst_verFam_frobPolyFam k

theorem frobenius_verschiebungInt_eq_smul [Φ.IsComm] (f : CartierModule p Φ) :
    frobenius (verschiebungInt f) = (p : WittVector p R) • f := by
  rw [frobenius_verschiebungInt, natCast_smul_eq_nsmul']

theorem smul_verschiebungInt [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    w • verschiebungInt f = verschiebungInt (WittVector.frobenius w • f) := by
  apply CartierModule.ext
  funext j
  change (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact WittLaw.subst_mulFam_frobPolyFam w n

theorem homothety_verschiebungInt [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    homothety a (verschiebungInt f) = verschiebungInt (homothety (a ^ p) f) := by
  apply CartierModule.ext
  funext j
  change (precomp _ (precomp _ f)).toPowerSeries j = (precomp _ (precomp _ f)).toPowerSeries j
  rw [precomp_precomp, precomp_precomp]
  congr 1
  funext n
  exact WittLaw.subst_teichFam_frobPolyFam a n

theorem teichmuller_smul_verschiebungInt [Φ.IsComm] (a : R) (f : CartierModule p Φ) :
    WittVector.teichmuller p a • verschiebungInt f =
      verschiebungInt (WittVector.teichmuller p (a ^ p) • f) := by
  rw [teichmuller_smul, teichmuller_smul, homothety_verschiebungInt]

theorem map_verschiebungInt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map φ (verschiebungInt f) = verschiebungInt (map φ f) :=
  map_precomp φ _ f

theorem endAct_verschiebungInt [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ (verschiebungInt f) = verschiebungInt (endAct φ f) :=
  map_precomp φ _ f

theorem verschiebungInt_nsmul [Φ.IsComm] (n : ℕ) (f : CartierModule p Φ) :
    verschiebungInt (n • f) = n • verschiebungInt f :=
  map_nsmul _ _ _

theorem toPowerSeries_verschiebungInt_iterate [Φ.IsComm] (f : CartierModule p Φ) (N : ℕ)
    (j : Fin d) :
    ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] f).toPowerSeries j =
      (fun g : MvPowerSeries ℕ R => subst (WittLaw.frobPolyFam p R) g)^[N] (f.toPowerSeries j) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change subst _ (((⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] f).toPowerSeries j) = _
    rw [ih]

theorem curve_verschiebungInt [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    curve (verschiebungInt f) j = PowerSeries.expand p hp.out.ne_zero (curve f j) := by
  change subst (curveFam R) (subst (WittLaw.frobPolyFam p R) (f.toPowerSeries j)) =
    MvPowerSeries.expand p hp.out.ne_zero (subst (curveFam R) (f.toPowerSeries j))
  rw [MvPowerSeries.expand, substAlgHom_apply,
    subst_comp_subst_apply WittLaw.hasSubst_frobPolyFam hasSubst_curveFam,
    subst_comp_subst_apply hasSubst_curveFam (HasSubst.X_pow hp.out.ne_zero)]
  congr 1
  funext n
  rw [WittLaw.subst_curveFam_frobPolyFam]
  cases n with
  | zero =>
    change (PowerSeries.X : PowerSeries R) ^ p =
      subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p) PowerSeries.X
    rw [PowerSeries.X, subst_X (HasSubst.X_pow hp.out.ne_zero)]
  | succ m =>
    change (0 : PowerSeries R) = subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p)
        (0 : PowerSeries R)
    rw [← coe_substAlgHom (HasSubst.X_pow hp.out.ne_zero), map_zero]

theorem tangent_verschiebungInt [Φ.IsComm] (f : CartierModule p Φ) :
    tangent (verschiebungInt f) = 0 := by
  funext j
  rw [← coeff_one_curve, curve_verschiebungInt, PowerSeries.coeff_expand, ite_eq_right]
  · rfl
  · intro h
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h)

namespace Examples

theorem frobenius_verschiebungInt_addLinear (v : Fin d → R) :
    frobenius (verschiebungInt (addLinear p v)) = (p : ℕ) • addLinear p v :=
  frobenius_verschiebungInt _

theorem tangent_verschiebungInt_addLinear (v : Fin d → R) :
    tangent (verschiebungInt (addLinear p v)) = 0 :=
  tangent_verschiebungInt _

end Examples

end CartierModule

end MvFormalGroup

end
