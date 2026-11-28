/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Perfectoid.CrystallineFrobenius
public import MathlibExt.RingTheory.Perfectoid.SemistablePeriodRingAbstract

/-!
# The Frobenius and the monodromy operator of Fontaine's rings `B_cris` and `B_st`

Let `A_cris = PadicComplexInt.CrystallineCompletion p ξ` with its Frobenius
`φ = PadicComplexInt.frobeniusCrystallineCompletion p ξ`, which commutes with the Galois action and
satisfies `φ(log [ε]) = p log [ε]`. We extend `φ`, as a `ℚ_[p]`-algebra map commuting with the
action of `Gal(ℚ̄_p/ℚ_p)`, to

* `B_cris^+ = A_cris[1/p]` (`PadicComplexInt.BCrisPlus.frobenius`; J.-M. Fontaine, *Le corps des
  périodes p-adiques*, Astérisque 223 (1994), Exposé II, §2.3.1 p. 78),
* `B_cris = B_cris^+[1/t]`, where `φ(t) = p t` is a unit (`PadicComplexInt.BCris.frobenius`,
  `PadicComplexInt.BCris.frobenius_algebraMap_logTeichmullerCrystalline`; Fontaine, *op. cit.*,
  §2.3.4 p. 79),
* `B_st = B_cris[X]`, `X` standing for `log [p̃]`, with `φ(X) = p X`
  (`PadicComplexInt.BSt.frobenius`, `PadicComplexInt.BSt.frobenius_X`; Fontaine, *op. cit.*,
  §3.2.1 pp. 81–82; J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*,
  (8.1) p. 194).

The Galois equivariance is `PadicComplexInt.BCrisPlus.frobenius_galois`,
`PadicComplexInt.BCris.frobenius_galois` and `PadicComplexInt.BSt.frobenius_galois`; on `B_st`
it uses `σ(X) = X + log [u_σ]` and `φ(log [u_σ]) = p log [u_σ]`.

The monodromy operator `N = -d/dX` of `B_st` (`PadicComplexInt.BSt.monodromy`) is the unique
`B_cris`-derivation with `N(X) = -1` (`PadicComplexInt.BSt.eq_monodromy`); it satisfies
`N φ = p φ N` (`PadicComplexInt.BSt.monodromy_frobenius`) and commutes with the Galois action
(`PadicComplexInt.BSt.monodromy_galois`), as in Fontaine–Ouyang, Definition 8.5 and
Proposition 8.6 p. 194. Fontaine, *op. cit.*, §§3.2.2–3.2.3 p. 82, uses the opposite sign,
`N(log [b]) = v(b)`, which has the same two properties.
-/

@[expose] public noncomputable section

open Polynomial

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))
local notation "𝔸cris" => CrystallineCompletion p (xi p)

/-! ### `B_cris^+` -/

namespace BCrisPlus

/-- The Frobenius of `A_cris` extends the Frobenius of `W(𝓞_ℂ_[p]♭)`. -/
theorem frobeniusCrystallineCompletion_ofWittVector (a : 𝔸) :
    frobeniusCrystallineCompletion p (xi p) (ofWittVector p a) =
      ofWittVector p (WittVector.frobenius a) := by
  refine (frobeniusCrystallineCompletion_algebraMap p (xi p) _).trans
    (congrArg _ (Subtype.ext ?_))
  rw [coe_frobeniusFiniteDividedPowers]
  exact frobeniusLocalization_algebraMap p a

/-- `W(𝓞_ℂ_[p]♭)[1/p] → B_cris^+` extends `W(𝓞_ℂ_[p]♭) → A_cris`. -/
private theorem ofLocalizationAway_algebraMap (a : 𝔸) :
    ofLocalizationAway p (algebraMap 𝔸 𝔸ₚ a) =
      algebraMap 𝔸cris (BCrisPlus p) (ofWittVector p a) := by
  simp only [ofLocalizationAway, Localization.awayLift, IsLocalization.Away.lift_eq,
    RingHom.comp_apply]

/-- The image of `z ∈ ℤ_[p]` in `B_cris^+` is the image of `z ∈ W(𝓞_ℂ_[p]♭)` in `A_cris`. -/
private theorem algebraMap_padicInt (z : ℤ_[p]) :
    algebraMap ℚ_[p] (BCrisPlus p) (z : ℚ_[p]) =
      algebraMap 𝔸cris (BCrisPlus p) (ofWittVector p (padicIntToAinf p z)) := by
  change ofLocalizationAway p (padicToLocalizationAway p z) = _
  rw [padicToLocalizationAway_coe, ofLocalizationAway_algebraMap]

/-- A ring endomorphism of `B_cris^+` extending the Frobenius of `A_cris` fixes `ℚ_[p]`. -/
private theorem map_algebraMap_of_frobenius {g : BCrisPlus p →+* BCrisPlus p}
    (hg : ∀ x, g (algebraMap 𝔸cris (BCrisPlus p) x) =
      algebraMap 𝔸cris (BCrisPlus p) (frobeniusCrystallineCompletion p (xi p) x)) (r : ℚ_[p]) :
    g (algebraMap ℚ_[p] (BCrisPlus p) r) = algebraMap ℚ_[p] (BCrisPlus p) r := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    (j := g.comp (algebraMap ℚ_[p] (BCrisPlus p))) (RingHom.ext fun z => ?_)) r
  simp only [RingHom.comp_apply, PadicInt.algebraMap_apply]
  rw [algebraMap_padicInt, hg, frobeniusCrystallineCompletion_ofWittVector,
    WittVector.frobenius_eq_map_frobenius, map_padicIntToAinf]

/-- **The Frobenius of `B_cris^+ = A_cris[1/p]`**, induced by the Frobenius of `A_cris`; it is
`ℚ_[p]`-linear. -/
def frobenius : BCrisPlus p →ₐ[ℚ_[p]] BCrisPlus p :=
  { IsLocalization.Away.lift (S := BCrisPlus p) (p : 𝔸cris)
      (g := (algebraMap 𝔸cris (BCrisPlus p)).comp (frobeniusCrystallineCompletion p (xi p))) (by
        rw [RingHom.comp_apply, map_natCast, map_natCast]
        have := IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus p) (p : 𝔸cris)
        rwa [map_natCast] at this) with
    commutes' := by
      exact map_algebraMap_of_frobenius p (IsLocalization.Away.lift_eq (S := BCrisPlus p) _ _) }

/-- On `A_cris`, the Frobenius of `B_cris^+` is the Frobenius of `A_cris`. -/
theorem frobenius_algebraMap (x : 𝔸cris) :
    frobenius p (algebraMap 𝔸cris (BCrisPlus p) x) =
      algebraMap 𝔸cris (BCrisPlus p) (frobeniusCrystallineCompletion p (xi p) x) := by
  simp only [frobenius, AlgHom.coe_mk, IsLocalization.Away.lift_eq, RingHom.comp_apply]

/-- **The Frobenius of `B_cris^+` commutes with the Galois action.** -/
theorem frobenius_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCrisPlus p) :
    frobenius p (galois p σ x) = galois p σ (frobenius p x) := by
  have h : (frobenius p : BCrisPlus p →+* BCrisPlus p).comp (galois p σ : BCrisPlus p →+* _) =
      (galois p σ : BCrisPlus p →+* BCrisPlus p).comp (frobenius p : BCrisPlus p →+* _) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : 𝔸cris)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, RingHom.coe_coe, galois_algebraMap, frobenius_algebraMap,
        frobeniusCrystallineCompletion_galoisCrystallineCompletion])
  exact RingHom.congr_fun h x

end BCrisPlus

/-! ### `B_cris` -/

namespace BCris

/-- `p` is a unit of `B_cris`. -/
private theorem isUnit_natCast : IsUnit ((p : ℕ) : BCris p) := by
  rw [← map_natCast (algebraMap ℚ_[p] (BCris p))]
  exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)).map _

/-- The image in `B_cris` of `φ(t) = p t` is a unit. -/
private theorem isUnit_frobenius :
    IsUnit (((IsScalarTower.toAlgHom ℚ_[p] (BCrisPlus p) (BCris p)).comp
      (BCrisPlus.frobenius p))
        (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))) := by
  rw [AlgHom.comp_apply, BCrisPlus.frobenius_algebraMap,
    frobeniusCrystallineCompletion_logTeichmullerCrystalline, map_mul, map_natCast,
    IsScalarTower.toAlgHom_apply, map_mul, map_natCast]
  exact (isUnit_natCast p).mul (IsLocalization.Away.algebraMap_isUnit _)

/-- **The Frobenius of `B_cris = B_cris^+[1/t]`**, induced by the Frobenius of `B_cris^+`:
`φ(t) = p t` is a unit of `B_cris`. -/
def frobenius : BCris p →ₐ[ℚ_[p]] BCris p :=
  IsLocalization.Away.liftAlgHom (S := BCris p)
    (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p)))
    (f := (IsScalarTower.toAlgHom ℚ_[p] (BCrisPlus p) (BCris p)).comp (BCrisPlus.frobenius p))
    (by exact isUnit_frobenius p)

/-- On `B_cris^+`, the Frobenius of `B_cris` is the Frobenius of `B_cris^+`. -/
theorem frobenius_algebraMap (x : BCrisPlus p) :
    frobenius p (algebraMap (BCrisPlus p) (BCris p) x) =
      algebraMap (BCrisPlus p) (BCris p) (BCrisPlus.frobenius p x) := by
  rw [frobenius, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- On `A_cris`, the Frobenius of `B_cris` is the Frobenius of `A_cris`. -/
theorem frobenius_algebraMap_crystallineCompletion (x : 𝔸cris) :
    frobenius p (algebraMap 𝔸cris (BCris p) x) =
      algebraMap 𝔸cris (BCris p) (frobeniusCrystallineCompletion p (xi p) x) := by
  rw [IsScalarTower.algebraMap_apply 𝔸cris (BCrisPlus p) (BCris p), frobenius_algebraMap,
    BCrisPlus.frobenius_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **`φ(t) = p t`** in `B_cris`, for `t = log [ε]` and `ε = (1, ζ_p, ζ_{p²}, …)`. -/
theorem frobenius_algebraMap_logTeichmullerCrystalline :
    frobenius p (algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p (untilt_epsilon p))) =
      (p : BCris p) * algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p (untilt_epsilon p))
    := by
  rw [frobenius_algebraMap_crystallineCompletion,
    frobeniusCrystallineCompletion_logTeichmullerCrystalline, map_mul, map_natCast]

/-- **The Frobenius of `B_cris` commutes with the Galois action.** -/
theorem frobenius_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BCris p) :
    frobenius p (galois p σ x) = galois p σ (frobenius p x) := by
  have h : (frobenius p : BCris p →+* BCris p).comp (galois p σ : BCris p →+* BCris p) =
      (galois p σ : BCris p →+* BCris p).comp (frobenius p : BCris p →+* BCris p) :=
    IsLocalization.ringHom_ext (Submonoid.powers
      (algebraMap 𝔸cris (BCrisPlus p) (logTeichmullerCrystalline p (untilt_epsilon p))))
      (RingHom.ext fun y => by
        simp only [RingHom.comp_apply, RingHom.coe_coe, galois_algebraMap, frobenius_algebraMap,
          BCrisPlus.frobenius_galois])
  exact RingHom.congr_fun h x

end BCris

/-! ### `B_st` -/

namespace BSt

/-- **The Frobenius of `B_st = B_cris[X]`**: the Frobenius of `B_cris` on the coefficients and
`φ(X) = p X`, as `X` stands for `log [p̃]` and `φ([p̃]) = [p̃]^p`. -/
def frobenius : BSt p →ₐ[ℚ_[p]] BSt p :=
  eval₂AlgHom ((IsScalarTower.toAlgHom ℚ_[p] (BCris p) (BSt p)).comp (BCris.frobenius p))
    ((p : BSt p) * X) fun _ => Commute.all _ _

/-- The Frobenius of `B_st` is the Frobenius of `B_cris` on the coefficients. -/
theorem frobenius_C (b : BCris p) : frobenius p (C b) = C (BCris.frobenius p b) :=
  eval₂_C _ _

/-- **`φ(X) = p X`** in `B_st = B_cris[X]`. -/
theorem frobenius_X : frobenius p X = (p : BSt p) * X :=
  eval₂_X _ _

/-- `φ(log [u]) = p log [u]` in `B_cris`, for `u♯ = 1`. -/
private theorem frobenius_algebraMap_logTeichmullerCrystalline {u : PreTilt 𝓞_ℂ_[p] p}
    (h : u.untilt = 1) :
    BCris.frobenius p (algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p h)) =
      (p : BCris p) * algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p h) := by
  rw [BCris.frobenius_algebraMap_crystallineCompletion,
    frobeniusCrystallineCompletion_logTeichmullerCrystalline, map_mul, map_natCast]

/-- **The Frobenius of `B_st` commutes with the Galois action**: on `X` this is
`φ(X + log [u_σ]) = p X + p log [u_σ] = σ(p X)`. -/
theorem frobenius_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : BSt p) :
    frobenius p (galois p σ x) = galois p σ (frobenius p x) := by
  have h : (frobenius p : BSt p →+* BSt p).comp (galois p σ : BSt p →+* BSt p) =
      (galois p σ : BSt p →+* BSt p).comp (frobenius p : BSt p →+* BSt p) := by
    refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · simp only [RingHom.comp_apply, RingHom.coe_coe, galois_C, frobenius_C,
        BCris.frobenius_galois]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, galois_X, frobenius_X, map_add, map_mul,
        map_natCast, frobenius_C, frobenius_algebraMap_logTeichmullerCrystalline]
      rw [← map_natCast (C : BCris p →+* BSt p)]
      ring
  exact RingHom.congr_fun h x

/-- The Galois action on `B_st` is `P ↦ (σ P)(X + log [u_σ])`, with `σ` acting on the
coefficients. -/
private theorem galois_eq_comp (σ : Gal(PadicAlgCl p/ℚ_[p])) (P : BSt p) :
    galois p σ P = (P.map (BCris.galois p σ : BCris p →+* BCris p)).comp (X + C
      (algebraMap 𝔸cris (BCris p) (logTeichmullerCrystalline p (untilt_kummerUnit p σ)))) := by
  rw [galois, eval₂AlgHom_apply, comp, eval₂_map]
  rfl

/-- The Frobenius of `B_st` is `P ↦ (φ P)(p X)`, with `φ` acting on the coefficients. -/
private theorem frobenius_eq_comp (P : BSt p) :
    frobenius p P = (P.map (BCris.frobenius p : BCris p →+* BCris p)).comp ((p : BSt p) * X) := by
  rw [frobenius, eval₂AlgHom_apply, comp, eval₂_map]
  rfl

/-- **The monodromy operator `N = -d/dX` of `B_st = B_cris[X]`**, a `B_cris`-derivation. -/
def monodromy : Derivation (BCris p) (BSt p) (BSt p) :=
  -derivative'

/-- `N P = -dP/dX`. -/
theorem monodromy_apply (P : BSt p) : monodromy p P = -derivative P :=
  rfl

/-- **`N(X) = -1`.** -/
theorem monodromy_X : monodromy p X = -1 := by
  rw [monodromy_apply, derivative_X]

/-- `N` vanishes on `B_cris`. -/
theorem monodromy_C (b : BCris p) : monodromy p (C b) = 0 := by
  rw [monodromy_apply, derivative_C, neg_zero]

/-- `N` is the unique `B_cris`-derivation of `B_st` with `N(X) = -1`. -/
theorem eq_monodromy {D : Derivation (BCris p) (BSt p) (BSt p)} (h : D X = -1) :
    D = monodromy p :=
  derivation_ext (h.trans (monodromy_X p).symm)

/-- **`N φ = p φ N`** on `B_st`. -/
theorem monodromy_frobenius (P : BSt p) :
    monodromy p (frobenius p P) = (p : BSt p) * frobenius p (monodromy p P) := by
  rw [monodromy_apply, monodromy_apply, frobenius_eq_comp, frobenius_eq_comp, derivative_comp,
    derivative_map, Polynomial.map_neg, neg_comp, derivative_mul, derivative_natCast,
    derivative_X]
  ring

/-- **`N` commutes with the Galois action** on `B_st`. -/
theorem monodromy_galois (σ : Gal(PadicAlgCl p/ℚ_[p])) (P : BSt p) :
    monodromy p (galois p σ P) = galois p σ (monodromy p P) := by
  rw [monodromy_apply, monodromy_apply, galois_eq_comp, galois_eq_comp, derivative_comp,
    derivative_map, derivative_X_add_C, one_mul, Polynomial.map_neg, neg_comp]

end BSt

end PadicComplexInt
