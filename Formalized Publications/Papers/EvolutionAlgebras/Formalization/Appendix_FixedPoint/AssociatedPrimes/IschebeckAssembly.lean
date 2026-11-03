/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.AssociatedPrimes.QuotientDimensionFacts
import Appendix_FixedPoint.AssociatedPrimes.LesSesPackages
import Appendix_FixedPoint.AssociatedPrimes.PrimeFiltrationDevissage
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Regular.Category
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.SuccOrder
import Mathlib.Order.WithBot
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Order.Monoid.WithTop

/-!
# IschebeckAssembly assembly for the GapBase finite-dimensional close (D7)

`l_ischebeck` (Matsumura Theorem 17.1 for `r = dim N < ∞`, `k = grade`
possibly `⊤`): `Ext^i(N,M) = 0` for `i + r < k`, by induction on the
dimension bound `n`. The `r = 0` leg fires Rees
(`ModuleCat.subsingleton_ext_of_exists_isRegular`) with the in-leaf
Finding-A support replacement; the `r > 0` leg dispatches through the
amended L5 devissage (`< r` goes to the IH, `= r` goes through the
`x`-SES plus the NAK finale).

## Forced deviations from the design note (semantics unchanged)

* The design note's bound `↑i < k - r` does not elaborate: mathlib has no
  `Sub (WithBot ℕ∞)` instance (`HSub` synthesis fails). The statement
  uses the additive form `↑i + r < k` instead, which is equivalent under
  the `r < ⊤` fence (for truncated subtraction, `i + r < k ↔ i < k - r`
  at finite `k`, all degrees when `k = ⊤`, all degrees when `r = ⊥`).
  Numeric bounds use direct `ℕ → WithBot ℕ∞` casts for the
  `ENat.WithBot` discrete-step API. The UnmixedSqueeze interface call is at
  `i = 0` with `(0 : WithBot ℕ∞) + r < k`.
* The design note's Part A (X₃-as-ring-quotient) is skipped as redundant:
  Parts B + C already give `dim (R ⧸ ann N') ≤ dim (R ⧸ I) < r`
  with no ring structure on X₃ needed.
* Predecessor (`Nat`) induction instead of strong induction: every
  recursive call is at exactly the predecessor bound.

`[IsAlgClosed]`: not required and not used — everything here is over a
general commutative Noetherian local ring with no field hypotheses.

Wall-1: ascending only. `Q` never appears; filtration factors come
from L5 with no relation required; `N'` needs no primeness
(finiteness + dim-drop only). Wall-2: zero grade content in the
dimension arguments — only definitional/monotone facts (proved L1
lemmas + the in-leaf chain arguments); no `grade = height` or
C3a-shaped input anywhere. Proved (d) is dead and never cited.
-/

namespace AssociatedPrimes.IschebeckAssembly

open CategoryTheory Abelian

open scoped Pointwise

universe v

/-- Shared micro-lemma (public — UnmixedSqueeze imports it): the annihilator of
`R ⧸ P` as an `R`-module is `P`. Identifies `r = dim (R ⧸ P)` at the
`N = ModuleCat.of R (R ⧸ P)` call sites. -/
theorem annihilator_quot_primeQuot
    {R : Type v} [CommRing R] (P : Ideal R) [P.IsPrime] :
    (⊤ : Submodule R (R ⧸ P)).annihilator = P := by
  apply le_antisymm
  · intro r hr
    rw [Submodule.mem_annihilator] at hr
    have h0 : (Submodule.mkQ P) r = 0 := by
      have e : (Submodule.mkQ P) r = r • (Submodule.mkQ P) 1 := by
        rw [← map_smul _ _ _, smul_eq_mul, mul_one]
      rw [e]
      exact hr _ Submodule.mem_top
    rw [Submodule.mkQ_apply] at h0
    exact (Submodule.Quotient.mk_eq_zero P).mp h0
  · intro r hr
    rw [Submodule.mem_annihilator]
    intro q _
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective P q
    rw [← map_smul _ _ _, smul_eq_mul, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero P).mpr
      (Ideal.mul_mem_right s P hr)

/-- In-leaf Finding-A replacement support lemma (public in-leaf):
at `dim N = 0` the support is the singleton of the maximal ideal.
Proved from the prime pushforward / maximality pullback pattern;
proved (d) is dead for this call site and is never cited. -/
theorem support_eq_singleton_maximal_of_ann_dim_zero
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Nontrivial N]
    (h0 : ringKrullDim (R ⧸ (⊤ : Submodule R N).annihilator) ≤ 0) :
    Module.support R N = {⟨IsLocalRing.maximalIdeal R, inferInstance⟩} := by
  have h0' : Ring.KrullDimLE 0 (R ⧸ (⊤ : Submodule R N).annihilator) :=
    Ring.krullDimLE_iff.mpr h0
  have hall : ∀ I : Ideal (R ⧸ (⊤ : Submodule R N).annihilator),
      I.IsPrime → I.IsMaximal :=
    Ring.krullDimLE_zero_iff.mp h0'
  rw [Module.support_eq_zeroLocus]
  ext p
  simp only [Set.mem_singleton_iff, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hp
    have hpprime := p.isPrime
    have hle : Module.annihilator R N ≤ p.asIdeal := fun r hr => hp hr
    have hle' : (⊤ : Submodule R N).annihilator ≤ p.asIdeal := by
      rw [Submodule.annihilator_top]
      exact hle
    have hP' : (p.asIdeal.map
        (Ideal.Quotient.mk (⊤ : Submodule R N).annihilator)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hle'
    have hmax' : (p.asIdeal.map
        (Ideal.Quotient.mk (⊤ : Submodule R N).annihilator)).IsMaximal :=
      hall _ hP'
    have hsurj : Function.Surjective
        (Ideal.Quotient.mk (⊤ : Submodule R N).annihilator) :=
      Ideal.Quotient.mk_surjective
    have hmax : ((p.asIdeal.map
        (Ideal.Quotient.mk (⊤ : Submodule R N).annihilator)).comap
        (Ideal.Quotient.mk (⊤ : Submodule R N).annihilator)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ hsurj
    rw [Ideal.comap_map_mk hle'] at hmax
    have heq : p.asIdeal = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal hmax
    exact PrimeSpectrum.ext_iff.mpr heq
  · intro hp
    subst hp
    have hne : Module.annihilator R N ≠ ⊤ := by
      intro hcon
      obtain ⟨m, hm⟩ := exists_ne (0 : N)
      have h1 : (1 : R) ∈ Module.annihilator R N := by
        rw [hcon]
        exact Submodule.mem_top
      rw [Module.mem_annihilator] at h1
      have h10 := h1 m
      rw [one_smul] at h10
      exact hm h10
    have hle : Module.annihilator R N ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hne
    intro r hr
    change r ∈ IsLocalRing.maximalIdeal R
    exact hle hr

/-- Discrete step down: below `↑(n+1)` means at most `↑n`. -/
private lemma le_of_lt_succ {n : ℕ} {d : WithBot ℕ∞}
    (h : d < (((n + 1 : ℕ)) : WithBot ℕ∞)) :
    d ≤ (((n : ℕ)) : WithBot ℕ∞) := by
  have hcast : ((((n + 1 : ℕ))) : WithBot ℕ∞)
      = (((n : ℕ)) : WithBot ℕ∞) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast, ENat.WithBot.lt_add_one_iff] at h
  exact h

/-- Discrete step down through `+ 1`: `d + 1 ≤ ↑(n+1)` forces
`d ≤ ↑n`. Feeds the IH bound in the devissage and `x`-SES legs. -/
private lemma le_of_add_one_le_succ {n : ℕ} {d : WithBot ℕ∞}
    (h : d + 1 ≤ (((n + 1 : ℕ)) : WithBot ℕ∞)) :
    d ≤ (((n : ℕ)) : WithBot ℕ∞) := by
  have h1 : (1 : WithBot ℕ∞) ≠ ⊥ := by
    rw [← WithBot.coe_one]
    exact WithBot.coe_ne_bot
  have hle : d ≤ (((n + 1 : ℕ)) : WithBot ℕ∞) :=
    le_trans (WithBot.le_self_add h1 d) h
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact le_of_lt_succ hlt
  · subst heq
    exfalso
    rw [ENat.WithBot.add_one_le_iff] at h
    exact lt_irrefl _ h

/-- Every `d < ⊤` is bounded by some natural cast. Extracts the
induction bound from the `r < ⊤` fence. -/
private lemma exists_nat_bound {d : WithBot ℕ∞} (h : d < ⊤) :
    ∃ n : ℕ, d ≤ (((n : ℕ)) : WithBot ℕ∞) := by
  induction d with
  | bot =>
    exact ⟨0, bot_le⟩
  | coe t =>
    have ht : t ≠ ⊤ := by
      rintro rfl
      rw [WithBot.coe_top] at h
      exact lt_irrefl _ h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ht
    refine ⟨m, ?_⟩
    rw [← hm, WithBot.coe_natCast]

/-- Load-bearing NAK bridge: precomposition with `x • 𝟙 N` is the
`Module R (Ext N M i)` scalar action. One line via `mk₀` linearity. -/
private lemma precomp_smul_id_eq_smul {R : Type v} [CommRing R]
    [Small.{v} R] {N M : ModuleCat.{v} R}
    [CategoryTheory.HasExt.{v} (ModuleCat.{v} R)] {i : ℕ}
    (e : Ext N M i) (x : R) :
    (Ext.mk₀ (x • 𝟙 N)).comp e (zero_add i) = x • e := by
  rw [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]

/-- Trivial first variable: `Ext` out of a subsingleton module
vanishes at every degree (degree `0` by `homEquiv₀`, higher degrees
by projectivity of the zero object). -/
private lemma subsingleton_ext_of_subsingleton_first
    {R : Type v} [CommRing R] [Small.{v} R]
    {N M : ModuleCat.{v} R}
    [CategoryTheory.HasExt.{v} (ModuleCat.{v} R)]
    (hsub : Subsingleton (N : Type v)) (i : ℕ) :
    Subsingleton (Ext N M i) := by
  have h0 : ∀ q : (N : Type v), q = 0 := fun q => Subsingleton.elim q 0
  cases i with
  | zero =>
    have hHom : Subsingleton (N ⟶ M) :=
      ⟨fun f g => ModuleCat.hom_ext
        (LinearMap.ext fun q => by rw [h0 q, map_zero, map_zero])⟩
    exact Ext.homEquiv₀.subsingleton
  | succ n =>
    have hproj : Projective N := by
      refine ⟨?_⟩
      intro E X f e _
      exact ⟨0, by
        have hf0 : f = 0 :=
          ModuleCat.hom_ext (LinearMap.ext fun q => by
            change f.hom q = 0
            rw [h0 q, map_zero])
        rw [Limits.zero_comp]
        exact hf0.symm⟩
    exact Ext.subsingleton_of_projective _ _ n

/-- `x`-existence: a prime with positive quotient dimension is
strictly below the maximal ideal, so `∃ x ∈ 𝔪, x ∉ P`. -/
private lemma exists_mem_maximal_not_mem_of_dim_succ
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {P : Ideal R} [P.IsPrime] {n : ℕ}
    (hr : ringKrullDim (R ⧸ P) = (((n + 1 : ℕ)) : WithBot ℕ∞)) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ x ∉ P := by
  have hPne : P ≠ IsLocalRing.maximalIdeal R := by
    intro hcon
    have hmax : P.IsMaximal :=
      hcon.symm ▸ IsLocalRing.maximalIdeal.isMaximal R
    have hsub : Subsingleton (PrimeSpectrum (R ⧸ P)) := ⟨fun p q => by
      have key : ∀ Q : Ideal (R ⧸ P), Q.IsPrime →
          P = Q.comap (Ideal.Quotient.mk P) := by
        intro Q hQ
        apply hmax.eq_of_le
        · intro hconQ
          have h1 : (1 : R) ∈ Q.comap (Ideal.Quotient.mk P) := by
            rw [hconQ]
            exact Submodule.mem_top
          have h1' : (Ideal.Quotient.mk P) 1 ∈ Q := h1
          rw [map_one] at h1'
          exact hQ.ne_top ((Ideal.eq_top_iff_one _).mpr h1')
        · intro r hr
          have hz : (Ideal.Quotient.mk P) r = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr hr
          change (Ideal.Quotient.mk P) r ∈ Q
          rw [hz]
          exact Submodule.zero_mem Q
      have hconPQ : p.asIdeal.comap (Ideal.Quotient.mk P)
          = q.asIdeal.comap (Ideal.Quotient.mk P) := by
        rw [← key _ p.isPrime, ← key _ q.isPrime]
      have heq : p.asIdeal = q.asIdeal :=
        Ideal.comap_injective_of_surjective (Ideal.Quotient.mk P)
          Ideal.Quotient.mk_surjective hconPQ
      exact PrimeSpectrum.ext_iff.mpr heq⟩
    have hdim : ringKrullDim (R ⧸ P) ≤ 0 :=
      Order.krullDim_nonpos_of_subsingleton
    rw [hr] at hdim
    have hcast : ((((n + 1 : ℕ))) : WithBot ℕ∞)
        = (((n : ℕ)) : WithBot ℕ∞) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hcast] at hdim
    have hbot := (ENat.WithBot.add_one_le_zero_iff _).mp hdim
    have hnb : ((((n : ℕ))) : WithBot ℕ∞) ≠ ⊥ := by
      rw [← WithBot.coe_natCast]
      exact WithBot.coe_ne_bot
    exact hnb hbot
  have hle : P ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal_of_isPrime P
  have hlt : P < IsLocalRing.maximalIdeal R := lt_of_le_of_ne hle hPne
  obtain ⟨x, hxm, hxP⟩ := SetLike.exists_of_lt hlt
  exact ⟨x, hxm, hxP⟩

/-- Regularity: `x ∉ P` is `R ⧸ P`-regular, since `R ⧸ P` is a
domain and `x` acts as multiplication by a nonzero element. -/
private lemma isSMulRegular_quot_of_not_mem
    {R : Type v} [CommRing R] [IsNoetherianRing R]
    {P : Ideal R} [P.IsPrime] {x : R} (hxP : x ∉ P) :
    IsSMulRegular (R ⧸ P) x := by
  have hx0 : (Ideal.Quotient.mk P) x ≠ 0 := by
    intro hcon
    rw [Ideal.Quotient.eq_zero_iff_mem] at hcon
    exact hxP hcon
  intro a b hab
  have hsmul : ∀ q : R ⧸ P, x • q = (Ideal.Quotient.mk P) x * q := by
    intro q
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  change x • a = x • b at hab
  rw [hsmul, hsmul] at hab
  exact mul_right_injective₀ hx0 hab

/-- `x`-SES dim drop (Parts B + C): for `I := P ⊔ span {x}`,
`dim (R ⧸ ann N') ≤ dim (R ⧸ I) ≤ ↑n` where
`N' = (R ⧸ P) ⧸ x • ⊤`. Part B argues per minimal prime over `I`
via proved strictDrop + (e); Part C is the quotient-surjectivity
pattern from proved (e)'s proof fragment. -/
private lemma dim_quot_ann_smul_quot_le
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {P : Ideal R} [P.IsPrime] {n : ℕ}
    (hr : ringKrullDim (R ⧸ P) = (((n + 1 : ℕ)) : WithBot ℕ∞))
    {x : R} (hxP : x ∉ P) :
    ringKrullDim
        (R ⧸ (⊤ : Submodule R ((R ⧸ P) ⧸ x • (⊤ : Submodule R (R ⧸ P)))
          ).annihilator) ≤ (((n : ℕ)) : WithBot ℕ∞) := by
  have hsmul : ∀ (s : R) (q' : R ⧸ P),
      s • Submodule.mkQ (x • (⊤ : Submodule R (R ⧸ P))) q'
        = Submodule.mkQ (x • (⊤ : Submodule R (R ⧸ P))) (s • q') := by
    intro s q'
    simp
  have hIC : P ⊔ Ideal.span {x}
      ≤ (⊤ : Submodule R ((R ⧸ P) ⧸ x • (⊤ : Submodule R (R ⧸ P)))
        ).annihilator := by
    apply sup_le
    · intro s hs
      rw [Submodule.mem_annihilator]
      intro q _
      obtain ⟨q', rfl⟩ :=
        Submodule.mkQ_surjective (x • (⊤ : Submodule R (R ⧸ P))) q
      rw [hsmul]
      have hsann : s ∈ (⊤ : Submodule R (R ⧸ P)).annihilator := by
        rw [annihilator_quot_primeQuot P]
        exact hs
      rw [Submodule.mem_annihilator] at hsann
      have hz : s • q' = 0 := hsann q' Submodule.mem_top
      rw [hz, map_zero]
    · rw [Submodule.span_le]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      refine Submodule.mem_annihilator.mpr ?_
      intro q _
      obtain ⟨q', rfl⟩ :=
        Submodule.mkQ_surjective (x • (⊤ : Submodule R (R ⧸ P))) q
      rw [hsmul, Submodule.mkQ_apply]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨q', Submodule.mem_top, rfl⟩
  have hIJ : P ⊔ Ideal.span {x}
      ≤ ((⊤ : Submodule R ((R ⧸ P) ⧸ x • (⊤ : Submodule R (R ⧸ P)))
          ).annihilator).comap (RingHom.id R) := by
    rw [Ideal.comap_id]
    exact hIC
  have hsurj : Function.Surjective
      (Ideal.quotientMap _ (RingHom.id R) hIJ) :=
    Ideal.quotientMap_surjective (fun x => ⟨x, rfl⟩)
  have hC : ringKrullDim
      (R ⧸ (⊤ : Submodule R ((R ⧸ P) ⧸ x • (⊤ : Submodule R (R ⧸ P)))
        ).annihilator) ≤ ringKrullDim (R ⧸ P ⊔ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective _ hsurj
  have hB : ringKrullDim (R ⧸ P ⊔ Ideal.span {x})
      ≤ (((n : ℕ)) : WithBot ℕ∞) := by
    rw [AssociatedPrimes.QuotientDimensionFacts.ringKrullDim_quotient_eq_sup_minimalPrimes]
    apply iSup_le
    intro Q
    have hQmin : (P ⊔ Ideal.span {x}).IsMinimalPrime Q.1 := Q.2
    have hQprime : Q.1.IsPrime := Ideal.IsMinimalPrime.isPrime hQmin
    have hxQ : x ∈ Q.1 :=
      hQmin.le ((le_sup_right : Ideal.span {x} ≤ P ⊔ Ideal.span {x})
        (Submodule.mem_span_singleton_self x))
    have hPQ : P < Q.1 :=
      lt_of_le_of_ne (le_trans le_sup_left hQmin.le)
        (fun hcon => hxP (hcon ▸ hxQ))
    have hdrop :=
      AssociatedPrimes.QuotientDimensionFacts.ringKrullDim_quotient_strictDrop hPQ
    rw [hr] at hdrop
    exact le_of_add_one_le_succ hdrop
  exact le_trans hC hB

/-- NAK finale: surjective precomposition (wrapper B `.2`) makes
`Ext N M i` vanish, since the precomp action is the scalar action
and `x ∈ 𝔪` forces `⊤ ≤ 𝔪 • ⊤`. -/
private lemma subsingleton_ext_of_surjective_precomp
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] {N M : ModuleCat.{v} R}
    [Module.Finite R (N : Type v)] [Module.Finite R (M : Type v)]
    [CategoryTheory.HasExt.{v} (ModuleCat.{v} R)]
    {x : R} (hxm : x ∈ IsLocalRing.maximalIdeal R) {i : ℕ}
    (hsurj : Function.Surjective
      (fun e : Ext N M i => (Ext.mk₀ (x • 𝟙 N)).comp e (zero_add i))) :
    Subsingleton (Ext N M i) := by
  have hle : (⊤ : Submodule R (Ext N M i)) ≤
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R (Ext N M i)) := by
    intro e _
    obtain ⟨e', he'⟩ := hsurj e
    have hsmul : x • e' = e := by
      rw [← he']
      exact (precomp_smul_id_eq_smul e' x).symm
    rw [← hsmul]
    exact Submodule.smul_mem_smul hxm Submodule.mem_top
  have hFG : (⊤ : Submodule R (Ext N M i)).FG := Module.Finite.fg_top
  have hjac : IsLocalRing.maximalIdeal R ≤ Ideal.jacobson ⊥ :=
    IsLocalRing.maximalIdeal_le_jacobson ⊥
  have htop : (⊤ : Submodule R (Ext N M i)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hFG hle hjac
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊤ : Submodule R (Ext N M i)) := Submodule.mem_top
  have hb : b ∈ (⊤ : Submodule R (Ext N M i)) := Submodule.mem_top
  rw [htop, Submodule.mem_bot] at ha
  rw [htop, Submodule.mem_bot] at hb
  rw [ha, hb]

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GapGradeSeq

/-- IschebeckAssembly induction: `Ext`-vanishing for all finite `N` with
`dim N ≤ ↑n`, by predecessor induction on `n`. The `n = 0` leg is
Rees; the step splits `dim N < ↑(n+1)` (back to the IH) from
`dim N = ↑(n+1)` (amended devissage: `< r` to the IH, `= r`
through the `x`-SES plus the NAK finale). -/
private lemma ischebeck_aux
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] {M : ModuleCat.{v} R}
    [Module.Finite R (M : Type v)] [Nontrivial (M : Type v)]
    [CategoryTheory.HasExt.{v} (ModuleCat.{v} R)] :
    ∀ n : ℕ, ∀ (N : ModuleCat.{v} R),
      ∀ (_ : Module.Finite R (N : Type v)),
        ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator)
            ≤ (((n : ℕ)) : WithBot ℕ∞) →
        ∀ i : ℕ, (((i : ℕ)) : WithBot ℕ∞) +
            ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator) <
            ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (
              M : Type v)
              (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞) →
          Subsingleton (Ext N M i) := by
  intro n
  induction n with
  | zero =>
    intro N hfinN hNbound i hi
    have h0 : ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator)
        ≤ 0 := by
      simpa using hNbound
    have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R (M : Type v))
        < ⊤ :=
      lt_top_iff_ne_top.mpr AssociatedPrimes.QuotientDimensionFacts.maximalIdeal_smul_ne_top
    by_cases hN : Nontrivial (N : Type v)
    · have hsupp : Module.support R (N : Type v) ⊆
          PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Ideal R) := by
        rw [support_eq_singleton_maximal_of_ann_dim_zero h0]
        rw [Set.singleton_subset_iff, PrimeSpectrum.mem_zeroLocus]
      by_cases htop :
          EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (M : Type v)
          (IsLocalRing.maximalIdeal R) = ⊤
      · obtain ⟨rs, hlen, hmem, hreg⟩ :=
          exists_isRegular_of_grade_eq_top
            (IsLocalRing.maximalIdeal R) htop (i + 1)
        have hi_len : i < rs.length := by omega
        exact ModuleCat.subsingleton_ext_of_exists_isRegular
          (IsLocalRing.maximalIdeal R) N hsupp M hsmul rs hmem hreg i hi_len
      · have hanne : (⊤ : Submodule R (N : Type v)).annihilator ≠ ⊤ := by
          intro hcon
          obtain ⟨m, hm⟩ := exists_ne (0 : (N : Type v))
          have h1 : (1 : R) ∈ (⊤ : Submodule R (N : Type v)).annihilator := by
            rw [hcon]
            exact Submodule.mem_top
          rw [Submodule.mem_annihilator] at h1
          have h10 := h1 m Submodule.mem_top
          rw [one_smul] at h10
          exact hm h10
        have hnontrivQ : Nontrivial
            (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator) :=
          Ideal.Quotient.nontrivial_iff.mpr hanne
        have hnn : (0 : WithBot ℕ∞) ≤
            ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator) :=
          ringKrullDim_nonneg_of_nontrivial
        have hile : (((i : ℕ)) : WithBot ℕ∞) ≤ (((i : ℕ)) : WithBot ℕ∞) +
            ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator) := by
          calc (((i : ℕ)) : WithBot ℕ∞)
              = (((i : ℕ)) : WithBot ℕ∞) + 0 := (add_zero _).symm
            _ ≤ (((i : ℕ)) : WithBot ℕ∞) + _ := add_le_add le_rfl hnn
        have hilt : (((i : ℕ)) : WithBot ℕ∞) <
            ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (
              M : Type v)
              (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞) :=
          lt_of_le_of_lt hile hi
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
        have him : i < m := by
          have h1 := hilt
          rw [← hm, ← WithBot.coe_natCast, WithBot.coe_lt_coe,
            ENat.natCast_lt_natCast] at h1
          exact h1
        have hle : (((i + 1 : ℕ) : ℕ∞)) ≤
            EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (
              M : Type v)
              (IsLocalRing.maximalIdeal R) := by
          rw [← hm, ENat.natCast_le_natCast]
          omega
        obtain ⟨rs, hlen, hmem, hreg⟩ :=
          exists_isRegular_of_le_grade
            (IsLocalRing.maximalIdeal R) hle
        have hi_len : i < rs.length := by omega
        exact ModuleCat.subsingleton_ext_of_exists_isRegular
          (IsLocalRing.maximalIdeal R) N hsupp M hsmul rs hmem hreg i hi_len
    · rw [not_nontrivial_iff_subsingleton] at hN
      exact subsingleton_ext_of_subsingleton_first hN i
  | succ n ih =>
    intro N hfinN hNbound i hi
    have hcast : ((((n + 1 : ℕ))) : WithBot ℕ∞)
        = (((n : ℕ)) : WithBot ℕ∞) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have h1 : (1 : WithBot ℕ∞) ≠ ⊥ := by
      rw [← WithBot.coe_one]
      exact WithBot.coe_ne_bot
    have hnn1 : (((n : ℕ)) : WithBot ℕ∞)
        ≤ (((n + 1 : ℕ)) : WithBot ℕ∞) := by
      rw [hcast]
      exact WithBot.le_self_add h1 _
    rcases lt_or_eq_of_le hNbound with hlt | heq
    · have hleN : ringKrullDim
          (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator)
          ≤ (((n : ℕ)) : WithBot ℕ∞) := by
        rw [hcast, ENat.WithBot.lt_add_one_iff] at hlt
        exact hlt
      exact ih N hfinN hleN i hi
    · rw [heq] at hi
      refine
        AssociatedPrimes.PrimeFiltrationDevissage.subsingleton_ext_of_subsingleton_primeQuotients
        (Y := M) (n := i) ?_
      intro P hP hle
      rw [heq] at hle
      rcases lt_or_eq_of_le hle with hltP | heqP
      · have hleN : ringKrullDim (R ⧸ P)
            ≤ (((n : ℕ)) : WithBot ℕ∞) := by
          rw [hcast, ENat.WithBot.lt_add_one_iff] at hltP
          exact hltP
        have hannQP : (⊤ : Submodule R
            ((ModuleCat.of R (R ⧸ P)) : Type v)).annihilator = P :=
          annihilator_quot_primeQuot P
        have hleN' : ringKrullDim
            (R ⧸ (⊤ : Submodule R
              ((ModuleCat.of R (R ⧸ P)) : Type v)).annihilator)
            ≤ (((n : ℕ)) : WithBot ℕ∞) := by
          rw [hannQP]
          exact hleN
        have hfinQP : Module.Finite R (R ⧸ P) := inferInstance
        have hfinQP' : Module.Finite R
            ((ModuleCat.of R (R ⧸ P)) : Type v) := hfinQP
        have hi' : (((i : ℕ)) : WithBot ℕ∞) +
            ringKrullDim
              (R ⧸ (⊤ : Submodule R
                ((ModuleCat.of R (R ⧸ P)) : Type v)).annihilator) <
            ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (
              M : Type v)
              (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞) := by
          rw [hannQP]
          apply lt_of_le_of_lt _ hi
          exact add_le_add le_rfl (le_of_lt hltP)
        exact ih (ModuleCat.of R (R ⧸ P)) hfinQP' hleN' i hi'
      · obtain ⟨x, hxm, hxP⟩ :=
          exists_mem_maximal_not_mem_of_dim_succ heqP
        have hreg : IsSMulRegular (R ⧸ P) x :=
          isSMulRegular_quot_of_not_mem hxP
        have hreg' : IsSMulRegular
            ((ModuleCat.of R (R ⧸ P)) : Type v) x := hreg
        have hfinQP : Module.Finite R (R ⧸ P) := inferInstance
        have hfinQP' : Module.Finite R
            ((ModuleCat.of R (R ⧸ P)) : Type v) := hfinQP
        set N' : ModuleCat.{v} R :=
          (ModuleCat.smulShortComplex (ModuleCat.of R (R ⧸ P)) x).X₃
          with hN'def
        have hX₃ : N' =
            ModuleCat.of R ((R ⧸ P) ⧸ x • (⊤ : Submodule R (R ⧸ P))) :=
          rfl
        have hdimN' : ringKrullDim
            (R ⧸ (⊤ : Submodule R (N' : Type v)).annihilator)
            ≤ (((n : ℕ)) : WithBot ℕ∞) := by
          rw [hX₃]
          change ringKrullDim
            (R ⧸ (⊤ : Submodule R
              ((R ⧸ P) ⧸ x • (⊤ : Submodule R (R ⧸ P)))).annihilator) ≤ _
          exact dim_quot_ann_smul_quot_le heqP hxP
        have hfinN' : Module.Finite R
            ((R ⧸ P) ⧸ x • (⊤ : Submodule R (R ⧸ P))) := inferInstance
        have hfinN'' : Module.Finite R (N' : Type v) := by
          rw [hX₃]
          exact hfinN'
        have hiN' : (((i : ℕ)) : WithBot ℕ∞) +
            ringKrullDim (R ⧸ (⊤ : Submodule R (N' : Type v)).annihilator) <
            ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (
              M : Type v)
              (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞) := by
          apply lt_of_le_of_lt _ hi
          apply add_le_add le_rfl
          exact le_trans hdimN' hnn1
        have hiN'' : (((i + 1 : ℕ)) : WithBot ℕ∞) +
            ringKrullDim (R ⧸ (⊤ : Submodule R (N' : Type v)).annihilator) <
            ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (
              M : Type v)
              (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞) := by
          have hcastI : ((((i + 1 : ℕ))) : WithBot ℕ∞)
              = (((i : ℕ)) : WithBot ℕ∞) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          rw [hcastI]
          have heq2 : ((((i : ℕ)) : WithBot ℕ∞) + 1) +
              ringKrullDim (R ⧸ (⊤ : Submodule R (N' : Type v)).annihilator)
              = (((i : ℕ)) : WithBot ℕ∞) +
                (ringKrullDim
                  (R ⧸ (⊤ : Submodule R (N' : Type v)).annihilator) + 1) := by
            ac_rfl
          rw [heq2]
          apply lt_of_le_of_lt _ hi
          apply add_le_add le_rfl
          have hstep : ringKrullDim
                (R ⧸ (⊤ : Submodule R (N' : Type v)).annihilator) + 1
              ≤ (((n : ℕ)) : WithBot ℕ∞) + 1 :=
            add_le_add hdimN' le_rfl
          rwa [← hcast] at hstep
        have h₃ : Subsingleton
            (Ext (ModuleCat.smulShortComplex (ModuleCat.of R (R ⧸ P)) x).X₃
              M i) :=
          ih N' hfinN'' hdimN' i hiN'
        have h₃' : Subsingleton
            (Ext (ModuleCat.smulShortComplex (ModuleCat.of R (R ⧸ P)) x).X₃
              M (i + 1)) :=
          ih N' hfinN'' hdimN' (i + 1) hiN''
        have hB := AssociatedPrimes.LesSesPackages.bijective_x_precomp_of_subsingleton_quot
          hreg' M (add_comm 1 i) h₃ h₃'
        exact subsingleton_ext_of_surjective_precomp hxm hB.2

/-- `L-ischebeck` (17.1 for `r = dim N < ∞`, `k = grade` possibly
`⊤`): `Ext^i(N,M)` vanishes for `i + r < k`. The `Nontrivial M`
hypothesis discharges D4; the `Nontrivial N` split is internal. -/
theorem l_ischebeck
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] {M N : ModuleCat.{v} R}
    [Module.Finite R (M : Type v)] [Module.Finite R (N : Type v)]
    [Nontrivial (M : Type v)]
    [CategoryTheory.HasExt.{v} (ModuleCat.{v} R)]
    (hfin : ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator)
      < ⊤) :
    ∀ i : ℕ, (((i : ℕ)) : WithBot ℕ∞) +
        ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator) <
        ((EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradeDepthFragment.grade R (M : Type v)
          (IsLocalRing.maximalIdeal R) : ℕ∞) : WithBot ℕ∞) →
      Subsingleton (Ext N M i) := by
  intro i hi
  obtain ⟨n, hn⟩ := exists_nat_bound hfin
  exact ischebeck_aux n N inferInstance hn i hi

end AssociatedPrimes.IschebeckAssembly
