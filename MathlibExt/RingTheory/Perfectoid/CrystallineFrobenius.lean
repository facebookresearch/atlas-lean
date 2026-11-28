/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Perfectoid.CrystallinePeriodRingGalois
public import MathlibExt.RingTheory.Perfectoid.LogTeichmullerMultiple

/-!
# The Frobenius of Fontaine's crystalline period ring `A_cris`

Let `R = 𝓞_ℂ_[p]♭` (`PreTilt 𝓞_ℂ_[p] p`), a perfect ring of characteristic `p`, let
`A_inf = W(R)` and let `φ : A_inf → A_inf` be the Witt vector Frobenius (`WittVector.frobenius`),
which is bijective (`WittVector.frobenius_bijective`). For `w ∈ A_inf`, let
`A_cris = PadicComplexInt.CrystallineCompletion p w` be the `p`-adic completion of
`D = A_inf[w^n/n! : n ≥ 1] ⊆ A_inf[1/p]`; for a generator `w` of `ker θ` this is Fontaine's ring
(J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II, §2.3.3
p. 78). We show:

* `φ` lifts the Frobenius of `R`: `φ(x) ≡ x^p` modulo `p` (`WittVector.frobenius_sub_pow_mem_span`),
  so that `φ(w) = w^p + p a` (`PadicComplexInt.exists_frobenius_eq_pow_add`); for
  `ξ = p - [p♭]`, `φ(ξ) = p - [p♭ ^ p]` (`PadicComplexInt.frobenius_xi`). The Witt vector Frobenius
  is natural (`WittVector.map_frobenius`), so it commutes with the Galois action on `A_inf`.
* `φ` preserves `D`: `φ(w) = p z` with `z = a + (p - 1)! w^p/p! ∈ D`, hence
  `φ(w^n/n!) = (p^n/n!) zⁿ ∈ D` since `p^n/n! ∈ ℤ_p`
  (`PadicComplexInt.frobeniusLocalization_mem_finiteDividedPowers`; J.-M. Fontaine and Y. Ouyang,
  *Theory of p-adic Galois representations*, §7.1.3 p. 157). The induced map of `p`-adic
  completions is the Frobenius of `A_cris` (`PadicComplexInt.frobeniusCrystallineCompletion`;
  Fontaine, *op. cit.*, §2.2.3 d) p. 77); for a generator `w` of `ker θ`, it commutes with the
  Galois action (`PadicComplexInt.frobeniusCrystallineCompletion_galoisCrystallineCompletion`;
  Fontaine, *op. cit.*, §2.3.1 p. 78).
* `φ(log [ε]) = log [ε^p] = p log [ε]` in `A_cris = CrystallineCompletion p ξ` for `ε♯ = 1`
  (`PadicComplexInt.frobeniusCrystallineCompletion_logTeichmullerCrystalline`); for
  `ε = (1, ζ_p, ζ_{p²}, …)` this is `φ(t) = p t` (Fontaine, *op. cit.*, §2.3.4 p. 79;
  Fontaine–Ouyang, §7.1.3 p. 157). The proof writes `log [ε]` as the limit of the partial sums
  `Σ_{0<n<N} (-1)^(n+1) ([ε] - 1)ⁿ/n ∈ D`, which `φ` maps to the partial sums for `ε^p`.

`MathlibExt.RingTheory.SemiperfectCrystallinePeriodRings` presents `A_cris` of a semiperfect ring
through a universal divided power envelope supplied as data, with a supplied Frobenius of the
envelope (`HullFrobenius`); here the Frobenius of Fontaine's `A_cris` of `𝓞_ℂ_[p]` is constructed.
-/

@[expose] public noncomputable section

open Ideal PowerSeries
open WittVector (fontaineTheta)

/-! ### The Frobenius of Witt vectors -/

namespace WittVector

universe u

variable {p : ℕ} [hp : Fact p.Prime] {R S : Type u} [CommRing R] [CommRing S]

/-- **The Witt vector Frobenius is natural**: `W(f)(φ x) = φ(W(f) x)` for a ring map `f`. -/
theorem map_frobenius (f : R →+* S) (x : WittVector p R) :
    map f (frobenius x) = frobenius (map f x) :=
  (frobenius_isPoly p).map f x

/-- For a ring of characteristic `p`, the Witt vector Frobenius maps the Teichmüller
representative `[x]` to `[x ^ p]`. -/
theorem frobenius_teichmuller [CharP R p] (x : R) :
    frobenius (teichmuller p x) = teichmuller p (x ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]

/-- For a perfect ring `R` of characteristic `p`, the Witt vector Frobenius lifts the Frobenius
of `R`: `φ(x) ≡ x ^ p` modulo `p` in `W(R)`. -/
theorem frobenius_sub_pow_mem_span [CharP R p] [PerfectRing R p] (x : WittVector p R) :
    frobenius x - x ^ p ∈ Ideal.span {(p : WittVector p R)} := by
  rw [mem_span_p_iff_coeff_zero_eq_zero]
  change constantCoeff (frobenius x - x ^ p) = 0
  rw [map_sub, map_pow]
  change (frobenius x).coeff 0 - x.coeff 0 ^ p = 0
  rw [coeff_frobenius_charP, sub_self]

end WittVector

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔸" => WittVector p (PreTilt 𝓞_ℂ_[p] p)
local notation "𝔸ₚ" => Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))

/-! ### The Frobenius of `A_inf` -/

/-- **`φ(w) ≡ w ^ p` modulo `p`** in `W(𝓞_ℂ_[p]♭)`: `φ(w) = w ^ p + p a` for some `a`. -/
theorem exists_frobenius_eq_pow_add (w : 𝔸) :
    ∃ a : 𝔸, WittVector.frobenius w = w ^ p + (p : 𝔸) * a := by
  obtain ⟨a, ha⟩ := mem_span_singleton'.mp (WittVector.frobenius_sub_pow_mem_span w)
  exact ⟨a, by rw [mul_comm (p : 𝔸) a, ha]; ring⟩

/-- **`φ(ξ) = p - [p♭ ^ p]`** for `ξ = p - [p♭]`, the generator of the kernel of `θ`. -/
theorem frobenius_xi :
    WittVector.frobenius (xi p) = (p : 𝔸) - WittVector.teichmuller p (pFlat p ^ p) := by
  rw [xi, map_sub, map_natCast, WittVector.frobenius_teichmuller]

/-! ### The Frobenius of `A_inf[1/p]` -/

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[1/p]`, induced by the Witt vector Frobenius. -/
abbrev frobeniusLocalization : 𝔸ₚ →+* 𝔸ₚ :=
  Localization.awayMapNatCast (WittVector.frobenius : 𝔸 →+* 𝔸) p

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[1/p]` extends that of `W(𝓞_ℂ_[p]♭)`. -/
theorem frobeniusLocalization_algebraMap (a : 𝔸) :
    frobeniusLocalization p (algebraMap 𝔸 𝔸ₚ a) = algebraMap 𝔸 𝔸ₚ (WittVector.frobenius a) :=
  Localization.awayMapNatCast_algebraMap _ _ a

/-- `φ(w^n/n!) = φ(w)^n/n!` in `W(𝓞_ℂ_[p]♭)[1/p]`. -/
theorem frobeniusLocalization_dividedPower (w : 𝔸) (n : ℕ) :
    frobeniusLocalization p (dividedPower w n) = dividedPower (WittVector.frobenius w) n := by
  rw [dividedPower, dividedPower, map_mul, map_pow, frobeniusLocalization_algebraMap,
    IsUnit.map_ringInverse _ (isUnit_natCast_factorial n), map_natCast]

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[1/p]` commutes with the Galois action. -/
theorem frobeniusLocalization_galoisLocalization (σ : Gal(PadicAlgCl p/ℚ_[p])) (x : 𝔸ₚ) :
    frobeniusLocalization p (galoisLocalization p σ x) =
      galoisLocalization p σ (frobeniusLocalization p x) := by
  have h : (frobeniusLocalization p).comp (galoisLocalization p σ) =
      (galoisLocalization p σ).comp (frobeniusLocalization p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : 𝔸)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, Localization.awayMapNatCast_algebraMap,
        WittVector.map_frobenius])
  exact RingHom.congr_fun h x

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[1/p]` is injective. -/
theorem frobeniusLocalization_injective : Function.Injective (frobeniusLocalization p) := by
  have h : (Localization.awayMapNatCast
      (WittVector.frobeniusEquiv p (PreTilt 𝓞_ℂ_[p] p)).symm.toRingHom p).comp
        (frobeniusLocalization p) = RingHom.id 𝔸ₚ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (p : 𝔸)) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, Localization.awayMapNatCast_algebraMap, RingHom.id_apply]
    exact congrArg _ ((WittVector.frobeniusEquiv p _).symm_apply_apply a)
  exact Function.LeftInverse.injective (g := Localization.awayMapNatCast
    (WittVector.frobeniusEquiv p (PreTilt 𝓞_ℂ_[p] p)).symm.toRingHom p) (RingHom.congr_fun h)

/-! ### The Frobenius of `D = A_inf[w^n/n!]` -/

/-- `p ^ n / n! ∈ ℤ_p`: there is `e ∈ W(𝓞_ℂ_[p]♭)` with `n! e = p ^ n`. -/
theorem exists_factorial_mul_eq_pow (n : ℕ) :
    ∃ e : 𝔸, ((n.factorial : ℕ) : 𝔸) * e = (p : 𝔸) ^ n := by
  obtain ⟨v, m, hpm, hvm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p hp.out.ne_one
  have hv : v ≤ n := by
    have hmul : multiplicity p n.factorial = v := by
      refine multiplicity_eq_of_dvd_of_not_dvd ⟨m, hvm⟩ fun hd => hpm ?_
      rw [hvm, pow_succ] at hd
      exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos v) hd
    have h1 := hp.out.sub_one_mul_multiplicity_factorial (n := n)
    rw [hmul] at h1
    have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
    have h3 : v ≤ (p - 1) * v := Nat.le_mul_of_pos_left v h2
    omega
  have hm : IsUnit ((m : ℕ) : 𝔸) := by
    have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
    simpa only [map_natCast] using hu.map (padicIntToAinf p)
  obtain ⟨u, hu⟩ := hm.exists_right_inv
  refine ⟨(p : 𝔸) ^ (n - v) * u, ?_⟩
  rw [hvm, Nat.cast_mul, Nat.cast_pow]
  calc (p : 𝔸) ^ v * (m : 𝔸) * ((p : 𝔸) ^ (n - v) * u)
      = (p : 𝔸) ^ v * (p : 𝔸) ^ (n - v) * ((m : 𝔸) * u) := by ring
    _ = (p : 𝔸) ^ n := by rw [hu, mul_one, ← pow_add, Nat.add_sub_cancel' hv]

/-- `p ^ n / n!` lies in the image of `W(𝓞_ℂ_[p]♭)` in `W(𝓞_ℂ_[p]♭)[1/p]`. -/
theorem exists_natCast_pow_mul_inverse_factorial (n : ℕ) :
    ∃ e : 𝔸, (p : 𝔸ₚ) ^ n * Ring.inverse ((n.factorial : ℕ) : 𝔸ₚ) = algebraMap 𝔸 𝔸ₚ e := by
  obtain ⟨e, he⟩ := exists_factorial_mul_eq_pow p n
  refine ⟨e, ?_⟩
  have h := congrArg (algebraMap 𝔸 𝔸ₚ) he
  rw [map_mul, map_pow, map_natCast, map_natCast] at h
  rw [← h, mul_comm (((n.factorial : ℕ) : 𝔸ₚ)), mul_assoc,
    Ring.mul_inverse_cancel _ (isUnit_natCast_factorial n), mul_one]

/-- `φ(w) = p z` for some `z ∈ W(𝓞_ℂ_[p]♭)[w^n/n!]`: if `φ(w) = w ^ p + p a`, then
`z = a + (p - 1)! · w^p/p!`. -/
theorem exists_frobenius_eq_natCast_mul (w : 𝔸) :
    ∃ z ∈ finiteDividedPowers p w,
      algebraMap 𝔸 𝔸ₚ (WittVector.frobenius w) = (p : 𝔸ₚ) * z := by
  obtain ⟨a, ha⟩ := exists_frobenius_eq_pow_add p w
  refine ⟨algebraMap 𝔸 𝔸ₚ a + (((p - 1).factorial : ℕ) : 𝔸ₚ) * dividedPower w p,
    Subring.add_mem _ (algebraMap_mem_finiteDividedPowers w a)
      (Subring.mul_mem _ (natCast_mem _ _) (dividedPower_mem w p)), ?_⟩
  have hp' : ((p.factorial : ℕ) : 𝔸ₚ) = (p : 𝔸ₚ) * (((p - 1).factorial : ℕ) : 𝔸ₚ) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
  rw [ha, map_add, map_pow, map_mul, map_natCast, ← factorial_mul_dividedPower w p, hp']
  ring

/-- **`φ(D) ⊆ D`**: the Frobenius of `W(𝓞_ℂ_[p]♭)[1/p]` preserves
`D = W(𝓞_ℂ_[p]♭)[w^n/n!]`, as `φ(w^n/n!) = (p^n/n!) zⁿ` with `φ(w) = p z`, `z ∈ D` and
`p^n/n! ∈ ℤ_p`. -/
theorem frobeniusLocalization_mem_finiteDividedPowers (w : 𝔸) {x : 𝔸ₚ}
    (hx : x ∈ finiteDividedPowers p w) : frobeniusLocalization p x ∈ finiteDividedPowers p w := by
  obtain ⟨z, hz, hfz⟩ := exists_frobenius_eq_natCast_mul p w
  have h : finiteDividedPowers p w ≤
      (finiteDividedPowers p w).comap (frobeniusLocalization p) := by
    rw [finiteDividedPowers, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | ⟨n, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, frobeniusLocalization_algebraMap]
      exact algebraMap_mem_finiteDividedPowers w _
    · obtain ⟨e, he⟩ := exists_natCast_pow_mul_inverse_factorial p (n + 1)
      rw [SetLike.mem_coe, Subring.mem_comap, frobeniusLocalization_dividedPower, dividedPower,
        hfz, mul_pow, mul_right_comm, he]
      exact Subring.mul_mem _ (algebraMap_mem_finiteDividedPowers w e) (Subring.pow_mem _ hz _)
  exact h hx

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[w^n/n!]`: the restriction of the Frobenius of
`W(𝓞_ℂ_[p]♭)[1/p]`. -/
def frobeniusFiniteDividedPowers (w : 𝔸) : finiteDividedPowers p w →+* finiteDividedPowers p w :=
  (frobeniusLocalization p).restrict _ _ fun _ hx =>
    frobeniusLocalization_mem_finiteDividedPowers p w hx

/-- `frobeniusFiniteDividedPowers p w` is the restriction of the Frobenius of
`W(𝓞_ℂ_[p]♭)[1/p]`. -/
@[simp]
theorem coe_frobeniusFiniteDividedPowers (w : 𝔸) (x : finiteDividedPowers p w) :
    (frobeniusFiniteDividedPowers p w x : 𝔸ₚ) = frobeniusLocalization p x :=
  rfl

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[w^n/n!]` is injective. -/
theorem frobeniusFiniteDividedPowers_injective (w : 𝔸) :
    Function.Injective (frobeniusFiniteDividedPowers p w) := fun _ _ h =>
  Subtype.ext (frobeniusLocalization_injective p (congrArg Subtype.val h))

/-! ### The Frobenius of `A_cris` -/

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[w^n/n!]` maps the ideal `(p)` into itself. -/
theorem map_pIdeal_frobeniusFiniteDividedPowers_le (w : 𝔸) :
    (pIdeal w).map (frobeniusFiniteDividedPowers p w) ≤ pIdeal w := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- **The Frobenius of `A_cris`**: for `w ∈ W(𝓞_ℂ_[p]♭)`, the map of `p`-adic completions induced
by the Frobenius `frobeniusFiniteDividedPowers p w` of `W(𝓞_ℂ_[p]♭)[w^n/n!]`. For a generator `w`
of the kernel of `θ`, this is the Frobenius of Fontaine's `A_cris`. -/
def frobeniusCrystallineCompletion (w : 𝔸) :
    CrystallineCompletion p w →+* CrystallineCompletion p w :=
  AdicCompletion.mapRingHom (pIdeal w) (pIdeal w) (frobeniusFiniteDividedPowers p w)
    (map_pIdeal_frobeniusFiniteDividedPowers_le p w)

/-- On `W(𝓞_ℂ_[p]♭)[w^n/n!]`, the Frobenius of `A_cris` is the Frobenius of
`W(𝓞_ℂ_[p]♭)[w^n/n!]`. -/
theorem frobeniusCrystallineCompletion_algebraMap (w : 𝔸) (x : finiteDividedPowers p w) :
    frobeniusCrystallineCompletion p w
        (algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w) x) =
      algebraMap (finiteDividedPowers p w) (CrystallineCompletion p w)
        (frobeniusFiniteDividedPowers p w x) :=
  AdicCompletion.mapRingHom_of _ _ _ _ x

/-- Maps of adic completions induced by commuting ring maps commute. -/
private theorem mapRingHom_comp_comm {A : Type*} [CommRing A] (I : Ideal A) (f g : A →+* A)
    (hf : I.map f ≤ I) (hg : I.map g ≤ I) (h : f.comp g = g.comp f) :
    (AdicCompletion.mapRingHom I I f hf).comp (AdicCompletion.mapRingHom I I g hg) =
      (AdicCompletion.mapRingHom I I g hg).comp (AdicCompletion.mapRingHom I I f hf) := by
  rw [← AdicCompletion.mapRingHom_comp, ← AdicCompletion.mapRingHom_comp]
  congr 1

/-- **The Frobenius of `A_cris` commutes with the Galois action**: for a generator `w` of the
kernel of `θ`, `φ(σ x) = σ(φ x)`. -/
theorem frobeniusCrystallineCompletion_galoisCrystallineCompletion {w : 𝔸}
    (hgen : RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) = span {w}) (σ : Gal(PadicAlgCl p/ℚ_[p]))
    (x : CrystallineCompletion p w) :
    frobeniusCrystallineCompletion p w (galoisCrystallineCompletion p hgen σ x) =
      galoisCrystallineCompletion p hgen σ (frobeniusCrystallineCompletion p w x) :=
  RingHom.congr_fun (mapRingHom_comp_comm (pIdeal w) _ _
    (map_pIdeal_frobeniusFiniteDividedPowers_le p w)
    (map_pIdeal_galoisFiniteDividedPowers_le hgen σ)
    (RingHom.ext fun y => Subtype.ext (frobeniusLocalization_galoisLocalization p σ y))) x

/-- If the Frobenius maps the partial sums `Σ_{n<N} aₙ w^n/n!` of a restricted series `f` to the
partial sums of a restricted series `g`, then the Frobenius of `A_cris` maps the element defined
by `f` to the element defined by `g`. -/
theorem frobeniusCrystallineCompletion_ofRestricted (w : 𝔸) {f g : 𝔸⟦X⟧}
    (hf : f ∈ restrictedPowerSeries p) (hg : g ∈ restrictedPowerSeries p)
    (h : ∀ N, frobeniusLocalization p (dividedPowerSum w f N) = dividedPowerSum w g N) :
    frobeniusCrystallineCompletion p w (ofRestricted w hf) = ofRestricted w hg := by
  refine AdicCompletion.ext_evalₐ fun k => ?_
  -- Rewriting with these equations is slow at this ring, so they are chained by transitivity.
  have h₁ := AdicCompletion.evalₐ_mapRingHom (pIdeal w) (pIdeal w)
    (frobeniusFiniteDividedPowers p w) (map_pIdeal_frobeniusFiniteDividedPowers_le p w) k
    (ofRestricted w hf)
  have h₂ := congrArg (MathlibExt.RingTheory.AdicCompletionMaps.quotientMap (pIdeal w) (pIdeal w)
    (frobeniusFiniteDividedPowers p w) (map_pIdeal_frobeniusFiniteDividedPowers_le p w) k)
    (evalₐ_ofRestricted w hf k _ (le_max_left (decayBound hf k) (decayBound hg k)))
  have h₃ := evalₐ_ofRestricted w hg k _ (le_max_right (decayBound hf k) (decayBound hg k))
  refine h₁.trans (h₂.trans (Eq.trans ?_ h₃.symm))
  exact congrArg _ (Subtype.ext (h _))

/-! ### The Frobenius of `log [ε]` -/

/-- `p ^ k ∣ (p k)!`. -/
private theorem pow_dvd_factorial_mul (k : ℕ) : p ^ k ∣ (p * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_add, mul_one]
    exact (Nat.mul_dvd_mul ih (Nat.dvd_factorial hp.out.pos le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/-- The series `Σ_{n ≥ 1} (-1)^(n+1) (n-1)! cⁿ Xⁿ`, whose divided-power series at `w` is
`Σ_{n ≥ 1} (-1)^(n+1) (c w)ⁿ/n = log (1 + c w)`. -/
private def logSeriesCoeff (c : 𝔸) : 𝔸⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else (-1) ^ (n + 1) * (((n - 1).factorial : ℕ) : 𝔸) * c ^ n

/-- The series `Σ_{n ≥ 1} (-1)^(n+1) (n-1)! cⁿ Xⁿ` is restricted: `p^k ∣ (n-1)!` for `n > p k`. -/
private theorem logSeriesCoeff_mem (c : 𝔸) : logSeriesCoeff p c ∈ restrictedPowerSeries p := by
  refine (mem_restrictedPowerSeries p).2 fun k => ⟨p * k + 1, fun n hn => ?_⟩
  rw [logSeriesCoeff, PowerSeries.coeff_mk, ite_eq_right (by omega)]
  obtain ⟨d, hd⟩ := (pow_dvd_factorial_mul p k).trans
    (Nat.factorial_dvd_factorial (show p * k ≤ n - 1 by omega))
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨(d : 𝔸), ?_⟩ _) _
  rw [hd, Nat.cast_mul, Nat.cast_pow]

/-- The `n`-th term `(-1)^(n+1) (n-1)! yⁿ/n! = (-1)^(n+1) yⁿ/n` of `log (1 + y)`, `0` for
`n = 0`. -/
private def logTerm (n : ℕ) (y : 𝔸ₚ) : 𝔸ₚ :=
  if n = 0 then 0 else
    (-1) ^ (n + 1) * (((n - 1).factorial : ℕ) : 𝔸ₚ) * y ^ n * Ring.inverse ((n.factorial : ℕ) : 𝔸ₚ)

/-- The partial sums of `Σ_{n ≥ 1} (-1)^(n+1) (n-1)! cⁿ w^n/n!` are those of `log (1 + c w)`. -/
private theorem dividedPowerSum_logSeriesCoeff (w c : 𝔸) (N : ℕ) :
    dividedPowerSum w (logSeriesCoeff p c) N =
      ∑ n ∈ Finset.range N, logTerm p n (algebraMap 𝔸 𝔸ₚ (c * w)) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [logSeriesCoeff, PowerSeries.coeff_mk, logTerm, dividedPower]
  split_ifs
  · rw [map_zero, zero_mul]
  · simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring

/-- The Frobenius of `W(𝓞_ℂ_[p]♭)[1/p]` maps the terms of `log (1 + y)` to those of
`log (1 + φ(y))`. -/
private theorem frobeniusLocalization_logTerm (n : ℕ) (y : 𝔸ₚ) :
    frobeniusLocalization p (logTerm p n y) = logTerm p n (frobeniusLocalization p y) := by
  rw [logTerm, logTerm]
  split_ifs
  · exact map_zero _
  · rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast,
      IsUnit.map_ringInverse _ (isUnit_natCast_factorial n), map_natCast]

/-- The `n`-th term of the divided-power series of `f = Σ aₖ Xᵏ` at `w` is `aₙ w^n/n!`. -/
private theorem coeff_dividedPowerSeries_mul_pow (f : 𝔸⟦X⟧) (w : 𝔸) (n : ℕ) :
    PowerSeries.coeff n (dividedPowerSeries p f) * algebraMap 𝔸 𝔸ₚ w ^ n =
      algebraMap 𝔸 𝔸ₚ (PowerSeries.coeff n f) * dividedPower w n := by
  rw [dividedPowerSeries, PowerSeries.coeff_mk, dividedPower]
  ring

/-- `1/n = (n - 1)! · (1/n!)` in `W(𝓞_ℂ_[p]♭)[1/p]`, for `n ≠ 0`. -/
private theorem algebraMap_inv_natCast_eq {n : ℕ} (hn : n ≠ 0) :
    algebraMap ℚ_[p] 𝔸ₚ (n : ℚ_[p])⁻¹ =
      (((n - 1).factorial : ℕ) : 𝔸ₚ) * Ring.inverse ((n.factorial : ℕ) : 𝔸ₚ) := by
  apply (isUnit_natCast p hn).mul_left_cancel
  rw [natCast_mul_algebraMap_inv p hn, ← mul_assoc, ← Nat.cast_mul, Nat.mul_factorial_pred hn,
    Ring.mul_inverse_cancel _ (isUnit_natCast_factorial n)]

/-- For `ε♯ = 1`, `[ε] - 1 = c ξ` for some `c ∈ W(𝓞_ℂ_[p]♭)`. -/
private theorem exists_mul_xi_eq {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) :
    ∃ c : 𝔸, c * xi p = WittVector.teichmuller p ε - 1 := by
  have hk : WittVector.teichmuller p ε - 1 ∈ RingHom.ker (fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [RingHom.mem_ker, map_sub, map_one, WittVector.fontaineTheta_teichmuller, h, sub_self]
  rw [ker_fontaineTheta_eq_span_xi, Ideal.mem_span_singleton'] at hk
  exact hk

/-- If `[ε] - 1 = c ξ`, the image in `B_dR^+` of the element of `A_cris` defined by
`Σ_{n ≥ 1} (-1)^(n+1) (n-1)! cⁿ Xⁿ` is `log [ε]`. -/
private theorem toBDeRhamPlus_ofRestricted_logSeriesCoeff {ε : PreTilt 𝓞_ℂ_[p] p}
    (h : ε.untilt = 1) {c : 𝔸} (hc : c * xi p = WittVector.teichmuller p ε - 1) :
    toBDeRhamPlus (ker_fontaineTheta_eq_span_xi p) (ofRestricted (xi p) (logSeriesCoeff_mem p c)) =
      logTeichmuller p h := by
  rw [toBDeRhamPlus_ofRestricted, logTeichmuller, logOneAdd]
  refine AdicCompletion.evalPowerSeries_eq_of_coeff_mul_pow_eq _ _ _ _ _ fun n => ?_
  rw [coeff_dividedPowerSeries_mul_pow, coeff_logSeries, logSeriesCoeff, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  rw [ite_eq_right hn, ite_eq_right hn, ← hc, algebraMap_inv_natCast_eq p hn, dividedPower]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

/-- If `[ε] - 1 = c ξ`, then `log [ε] ∈ A_cris` is the element defined by
`Σ_{n ≥ 1} (-1)^(n+1) (n-1)! cⁿ Xⁿ`, the limit of the partial sums
`Σ_{0<n<N} (-1)^(n+1) ([ε] - 1)ⁿ/n`. -/
private theorem logTeichmullerCrystalline_eq_ofRestricted {ε : PreTilt 𝓞_ℂ_[p] p}
    (h : ε.untilt = 1) {c : 𝔸} (hc : c * xi p = WittVector.teichmuller p ε - 1) :
    logTeichmullerCrystalline p h = ofRestricted (xi p) (logSeriesCoeff_mem p c) :=
  toBDeRhamPlus_injective (ker_fontaineTheta_eq_span_xi p)
    ((toBDeRhamPlus_logTeichmullerCrystalline p h).trans
      (toBDeRhamPlus_ofRestricted_logSeriesCoeff p h hc).symm)

/-- **`φ(log [ε]) = log [ε ^ p]`** in `A_cris`, for `ε♯ = 1`: the Frobenius maps the partial sums
`Σ_{0<n<N} (-1)^(n+1) ([ε] - 1)ⁿ/n` to `Σ_{0<n<N} (-1)^(n+1) ([ε]^p - 1)ⁿ/n`, as
`φ([ε]) = [ε ^ p]`. -/
theorem frobeniusCrystallineCompletion_logTeichmullerCrystalline_eq {ε : PreTilt 𝓞_ℂ_[p] p}
    (h : ε.untilt = 1) (h' : (ε ^ p).untilt = 1) :
    frobeniusCrystallineCompletion p (xi p) (logTeichmullerCrystalline p h) =
      logTeichmullerCrystalline p h' := by
  obtain ⟨c, hc⟩ := exists_mul_xi_eq p h
  obtain ⟨c', hc'⟩ := exists_mul_xi_eq p h'
  rw [logTeichmullerCrystalline_eq_ofRestricted p h hc,
    logTeichmullerCrystalline_eq_ofRestricted p h' hc']
  refine frobeniusCrystallineCompletion_ofRestricted p (xi p) _ _ fun N => ?_
  rw [dividedPowerSum_logSeriesCoeff, dividedPowerSum_logSeriesCoeff, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [frobeniusLocalization_logTerm, frobeniusLocalization_algebraMap, hc, hc', map_sub, map_one,
    WittVector.frobenius_teichmuller]

/-- `log [εⁿ] = n log [ε]` in `A_cris`, for `ε♯ = 1`. -/
theorem logTeichmullerCrystalline_pow {ε : PreTilt 𝓞_ℂ_[p] p} (h : ε.untilt = 1) (n : ℕ)
    (hn : (ε ^ n).untilt = 1) :
    logTeichmullerCrystalline p hn =
      (n : CrystallineCompletion p (xi p)) * logTeichmullerCrystalline p h :=
  toBDeRhamPlus_injective (ker_fontaineTheta_eq_span_xi p) (by
    rw [map_mul, map_natCast, toBDeRhamPlus_logTeichmullerCrystalline,
      toBDeRhamPlus_logTeichmullerCrystalline, logTeichmuller_pow p h n hn])

/-- **`φ(log [ε]) = p log [ε]`** in `A_cris`, for `ε♯ = 1`; for `ε = (1, ζ_p, ζ_{p²}, …)`, this is
`φ(t) = p t` (Fontaine, *Le corps des périodes p-adiques*, Exposé II, §2.3.4 p. 79). -/
theorem frobeniusCrystallineCompletion_logTeichmullerCrystalline {ε : PreTilt 𝓞_ℂ_[p] p}
    (h : ε.untilt = 1) :
    frobeniusCrystallineCompletion p (xi p) (logTeichmullerCrystalline p h) =
      (p : CrystallineCompletion p (xi p)) * logTeichmullerCrystalline p h := by
  have h' : (ε ^ p).untilt = 1 := by rw [map_pow, h, one_pow]
  rw [frobeniusCrystallineCompletion_logTeichmullerCrystalline_eq p h h',
    logTeichmullerCrystalline_pow p h p h']

end PadicComplexInt
