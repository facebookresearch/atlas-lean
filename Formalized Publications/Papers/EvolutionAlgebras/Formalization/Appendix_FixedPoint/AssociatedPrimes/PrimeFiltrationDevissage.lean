/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.AssociatedPrimes.QuotientDimensionFacts
import Appendix_FixedPoint.AssociatedPrimes.LesSesPackages
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Prime-filtration devissage for the GapBase finite-dimensional close (D2)

This leaf proves the Thm-6.4-shape prime filtration existence
(`exists_primeFiltration`), the Ext-vanishing devissage along it
(`subsingleton_ext_of_subsingleton_primeQuotients`, amended §2b shape
per erratum E-L5a), and the factor-dimension bound (`factor_dim_le`,
the QuotientDimensionFacts dim-drop leg).

The filtration ascends (`⊥ = K₀ ≤ K₁ ≤ … ≤ K_k = ⊤`) with ACC
(`WellFoundedGT`) as termination; each factor `R ⧸ Pⱼ` is extracted
from the associated primes of the current quotient `M ⧸ K` and carries
no relation to any ambient prime. The annihilator-relative dimension
bound in the devissage hypothesis is discharged per factor by `F.hann`
plus `factor_dim_le`.

`[IsAlgClosed]`: not required and not used — everything here is over a
general commutative Noetherian ring with no field hypotheses at all.

Wall-1: ascending only. No prime is descended through a quotient:
`M ⧸ K` and `R ⧸ Pⱼ` appear only as objects of short complexes and the
first variable of `Ext`; `Q` never appears in this leaf at all.
Wall-2: zero grade content — the only dimension fact is the
pure-quotient-surjectivity `factor_dim_le` (the proved L1 (e) argument);
no `grade = height` or C3a-shaped input anywhere.
-/

namespace AssociatedPrimes.PrimeFiltrationDevissage

open CategoryTheory Abelian

universe v

/-- Auxiliary prime filtration of `M` from a base submodule `base`
(single ambient chain; steps stated with `≤`). The motive for the
`WellFoundedGT` existence induction: each step extends the base
upward. `PrimeFiltration` is this at `⊥`. -/
structure PrimeFiltrationFrom (R : Type v) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (base : Submodule R M) : Type v where
  k : ℕ
  K : Fin (k + 1) → Submodule R M
  hle : ∀ j : Fin k, K j.castSucc ≤ K j.succ
  hbot : K 0 = base
  htop : K (Fin.last k) = ⊤
  P : Fin k → Ideal R
  hprime : ∀ j, (P j).IsPrime
  hfactor : ∀ j, Nonempty
    ((↥(K j.succ) ⧸ (K j.castSucc).comap (K j.succ).subtype) ≃ₗ[R]
      (R ⧸ P j))
  hann : ∀ j, (⊤ : Submodule R M).annihilator ≤ P j

/-- Prime filtration of a finite module over a Noetherian ring
(Thm 6.4 shape, design note §2a): ascending chain from `⊥` to `⊤` with
prime-cyclic factors, each prime containing `ann M`. -/
abbrev PrimeFiltration (R : Type v) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Type v :=
  PrimeFiltrationFrom R M ⊥

/-- First-isomorphism bridge between the two quotient presentations of
a filtration step: the image of `T` in `M ⧸ S` is the quotient of `T`
by (the copy of) `S`. Used once to build `hfactor` (existence step)
and once to feed the SES left end (devissage step). -/
noncomputable def mapMkQEquivQuotComap {R : Type v} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (S T : Submodule R M) :
    ↥(T.map S.mkQ) ≃ₗ[R] ↥T ⧸ S.comap T.subtype := by
  let ψ : ↥T →ₗ[R] ↥(T.map S.mkQ) :=
    { toFun := fun t => ⟨S.mkQ t.1, Submodule.mem_map.mpr ⟨t.1, t.2, rfl⟩⟩
      map_add' := fun a b => by
        apply Subtype.ext
        change S.mkQ (a + b).1 = S.mkQ a.1 + S.mkQ b.1
        exact map_add S.mkQ a.1 b.1
      map_smul' := fun r a => by
        apply Subtype.ext
        change S.mkQ (r • a).1 = r • S.mkQ a.1
        exact map_smul S.mkQ r a.1 }
  have hker : LinearMap.ker ψ = S.comap T.subtype := by
    ext t
    rw [LinearMap.mem_ker, Submodule.mem_comap, Subtype.ext_iff]
    change (S.mkQ t.1 = 0) ↔ (T.subtype t ∈ S)
    rw [Submodule.mkQ_apply]
    exact Submodule.Quotient.mk_eq_zero S
  have hsurj : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨t, htT, htq⟩ := Submodule.mem_map.mp hq
    exact ⟨⟨t, htT⟩, Subtype.ext htq⟩
  have e := LinearMap.quotKerEquivOfSurjective ψ hsurj
  rw [hker] at e
  exact e.symm

/-- Extend a filtration from `K'` down to `K` by prepending one
prime-cyclic step (`K ≤ K'` with factor `≅ R ⧸ Pnew`). Chains and
prime lists extend by `Fin.cons`. -/
noncomputable def extendPartial {R : Type v} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {K K' : Submodule R M} (hleKK' : K ≤ K')
    (Pnew : Ideal R) (hprime0 : Pnew.IsPrime)
    (hfactor0 : Nonempty ((↥K' ⧸ K.comap K'.subtype) ≃ₗ[R] (R ⧸ Pnew)))
    (hann0 : (⊤ : Submodule R M).annihilator ≤ Pnew)
    (F' : PrimeFiltrationFrom R M K') : PrimeFiltrationFrom R M K where
  k := F'.k + 1
  K := Fin.cons (α := fun _ => Submodule R M) K F'.K
  hle := by
    intro j
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, F'.hbot]
      exact hleKK'
    | succ i =>
      simp only [Fin.castSucc_succ, Fin.cons_succ]
      exact F'.hle i
  hbot := by simp only [Fin.cons_zero]
  htop := by
    change (Fin.cons (α := fun _ => Submodule R M) K F'.K)
      ((Fin.last F'.k).succ) = ⊤
    rw [Fin.cons_succ]
    exact F'.htop
  P := Fin.cons (α := fun _ => Ideal R) Pnew F'.P
  hprime := by
    intro j
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact hprime0
    | succ i =>
      simp only [Fin.cons_succ]
      exact F'.hprime i
  hfactor := by
    intro j
    induction j using Fin.cases with
    | zero =>
      change Nonempty ((↥(F'.K 0) ⧸ K.comap (F'.K 0).subtype) ≃ₗ[R]
        (R ⧸ Pnew))
      rw [F'.hbot]
      exact hfactor0
    | succ i =>
      simp only [Fin.castSucc_succ]
      exact F'.hfactor i
  hann := by
    intro j
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      exact hann0
    | succ i =>
      simp only [Fin.cons_succ]
      exact F'.hann i

/-- Filtrations from any base exist: `WellFoundedGT` induction on
submodules (ascending `K`, i.e. well-founded on `>` — exactly ACC).
At each nontrivial quotient `M ⧸ K`, an associated prime gives an
injective `R ⧸ P ↪ M ⧸ K`; its range pulls back to `K' > K` with
prime-cyclic factor. The base `K = ⊤` closes with the empty tail. -/
theorem exists_primeFiltrationFrom {R : Type v} [CommRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (K : Submodule R M) :
    Nonempty (PrimeFiltrationFrom R M K) := by
  refine WellFoundedGT.induction
    (motive := fun K' => Nonempty (PrimeFiltrationFrom R M K')) K
    (fun K ih => ?_)
  by_cases hK : K = ⊤
  · subst hK
    refine ⟨?_⟩
    exact
      { k := 0
        K := fun _ => ⊤
        hle := fun j => j.elim0
        hbot := rfl
        htop := rfl
        P := fun j => j.elim0
        hprime := fun j => j.elim0
        hfactor := fun j => j.elim0
        hann := fun j => j.elim0 }
  · have hex : ∃ x : M ⧸ K, x ≠ 0 := by
      by_contra hcon
      apply hK
      rw [eq_top_iff]
      intro m _
      rw [← Submodule.Quotient.mk_eq_zero K]
      by_contra hne
      exact hcon ⟨_, hne⟩
    obtain ⟨x, hx⟩ := hex
    have : Nontrivial (M ⧸ K) := ⟨x, 0, hx⟩
    obtain ⟨P, hPmem⟩ := associatedPrimes.nonempty R (M ⧸ K)
    have hP : IsAssociatedPrime P (M ⧸ K) :=
      AssociatedPrimes.mem_iff.mp hPmem
    obtain ⟨hprime, g', hginj⟩ :=
      (isAssociatedPrime_iff_exists_injective_linearMap P (M ⧸ K)).mp hP
    set K' := (LinearMap.range g').comap (Submodule.mkQ K)
    have hRnontriv : Nontrivial (R ⧸ P) :=
      Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
    have hrange : LinearMap.range g' ≠ ⊥ := by
      intro hcon
      have h0 : g' = 0 := by
        refine LinearMap.ext fun y => ?_
        have hmem := LinearMap.mem_range_self g' y
        rw [hcon, Submodule.mem_bot] at hmem
        rw [LinearMap.zero_apply]
        exact hmem
      have hsub : Subsingleton (R ⧸ P) := ⟨fun a b => hginj (by simp [h0])⟩
      obtain ⟨a, b, hab⟩ := hRnontriv
      exact hab (hsub.elim a b)
    have hKlt : K < K' := by
      refine lt_of_le_of_ne ?hle ?hne
      · intro m hm
        change m ∈ (LinearMap.range g').comap (Submodule.mkQ K)
        rw [Submodule.mem_comap]
        have hmk : (Submodule.mkQ K) m = 0 := by
          rw [Submodule.mkQ_apply]
          exact (Submodule.Quotient.mk_eq_zero K).mpr hm
        rw [hmk]
        exact Submodule.zero_mem _
      · intro hcon
        apply hrange
        have hmap : (K'.map (Submodule.mkQ K)) = LinearMap.range g' :=
          Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective K) _
        have hmapK : (K.map (Submodule.mkQ K)) = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro y hy
          obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hy
          rw [Submodule.mkQ_apply]
          exact (Submodule.Quotient.mk_eq_zero K).mpr hm
        rw [← hcon, hmapK] at hmap
        exact hmap.symm
    obtain ⟨F'⟩ := ih K' hKlt
    have hannQ : (⊤ : Submodule R M).annihilator
        ≤ (⊤ : Submodule R (M ⧸ K)).annihilator := by
      intro r hr
      rw [Submodule.mem_annihilator] at hr ⊢
      intro q _
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective K q
      rw [← map_smul, hr m Submodule.mem_top, map_zero]
    have hann0 : (⊤ : Submodule R M).annihilator ≤ P :=
      le_trans hannQ (IsAssociatedPrime.annihilator_le hP)
    have hmap : (K'.map (Submodule.mkQ K)) = LinearMap.range g' :=
      Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective K) _
    have eRange : ↥(K'.map (Submodule.mkQ K)) ≃ₗ[R] ↥(LinearMap.range g') := by
      rw [hmap]
    have hfactor0 : Nonempty
        ((↥K' ⧸ K.comap K'.subtype) ≃ₗ[R] (R ⧸ P)) :=
      ⟨(mapMkQEquivQuotComap K K').symm.trans
        (eRange.trans (LinearEquiv.ofInjective g' hginj).symm)⟩
    exact ⟨extendPartial hKlt.le P hprime hfactor0 hann0 F'⟩

/-- Prime filtrations exist (Thm 6.4 shape, design note §2a). -/
theorem exists_primeFiltration {R : Type v} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Nonempty (PrimeFiltration R M) :=
  exists_primeFiltrationFrom ⊥

/-- Iso-transport for `Ext`-vanishing in the first variable (design note
§3c): precompose with `(Ext.mk₀ e.hom).comp` / `(Ext.mk₀ e.inv).comp`,
mutual inverses by the `mk₀` composition lemmas. -/
theorem subsingleton_ext_of_iso {R : Type v} [CommRing R] [Small.{v} R]
    {X X' Y : ModuleCat.{v} R} {n : ℕ} [HasExt.{v} (ModuleCat.{v} R)]
    (e : X ≅ X') (h : Subsingleton (Ext X Y n)) :
    Subsingleton (Ext X' Y n) := by
  have hGF : ∀ a : Ext X Y n,
      (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp a (zero_add n)) (zero_add n)
        = a := by
    intro a
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  have hFG : ∀ b : Ext X' Y n,
      (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp b (zero_add n)) (zero_add n)
        = b := by
    intro b
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  refine ⟨fun b₁ b₂ => ?_⟩
  have hEq := h.elim ((Ext.mk₀ e.hom).comp b₁ (zero_add n))
    ((Ext.mk₀ e.hom).comp b₂ (zero_add n))
  have hcongr := congrArg (fun a => (Ext.mk₀ e.inv).comp a (zero_add n)) hEq
  rw [hFG, hFG] at hcongr
  exact hcongr

/-- `Ext` out of `M ⧸ ⊤` vanishes: every element of `M ⧸ ⊤` is zero,
so maps out are trivial (degree `0` via `Ext.homEquiv₀`) and the
object is projective (higher degrees via
`Ext.subsingleton_of_projective`). The devissage base case. -/
theorem subsingleton_ext_quot_top {R : Type v} [CommRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (Y : ModuleCat.{v} R) (n : ℕ) [HasExt.{v} (ModuleCat.{v} R)] :
    Subsingleton
      (Ext (ModuleCat.of R (M ⧸ (⊤ : Submodule R M))) Y n) := by
  have h0 : ∀ q : M ⧸ (⊤ : Submodule R M), q = 0 := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (⊤ : Submodule R M) q
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero ⊤).mpr Submodule.mem_top
  cases n with
  | zero =>
    have hHom : Subsingleton
        (ModuleCat.of R (M ⧸ (⊤ : Submodule R M)) ⟶ Y) :=
      ⟨fun f g => ModuleCat.hom_ext
        (LinearMap.ext fun q => by rw [h0 q, map_zero, map_zero])⟩
    exact Ext.homEquiv₀.subsingleton
  | succ n =>
    have hproj : Projective
        (ModuleCat.of R (M ⧸ (⊤ : Submodule R M))) := by
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

/-- Factor-dimension bound (dim-drop leg, design note §2c): each filtration
prime contains `ann M`, so `R ⧸ Pⱼ` is a quotient of `R ⧸ ann M`.
Instantiates the proved L1 (e) argument at `ann M ≤ Pⱼ`. -/
theorem factor_dim_le {R : Type v} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : PrimeFiltration R M) (j : Fin F.k) :
    ringKrullDim (R ⧸ F.P j) ≤
      ringKrullDim (R ⧸ (⊤ : Submodule R M).annihilator) := by
  have hIJ : (⊤ : Submodule R M).annihilator ≤ (F.P j).comap (RingHom.id R) := by
    rw [Ideal.comap_id]
    exact F.hann j
  have hsurj : Function.Surjective
      (Ideal.quotientMap (F.P j) (RingHom.id R) hIJ) :=
    Ideal.quotientMap_surjective (fun x => ⟨x, rfl⟩)
  exact ringKrullDim_le_of_surjective _ hsurj

/-- PrimeFiltrationDevissage (`L-devissage`, design note §2b as amended by erratum E-L5a):
`Ext`-vanishing at all annihilator-dim-bounded prime quotients
implies vanishing at `N`. Descending induction on the filtration
(`Fin.reverseInduction`): the `⊤` end is `subsingleton_ext_quot_top`,
each step closes by proved wrapper A (`LesSesPackages`) on the submodule
SES, with ends identified by the third iso and `F.hfactor`; the `⊥`
end transports to `N`. The per-factor dim bound is discharged by
`F.hann` + `factor_dim_le`. -/
theorem subsingleton_ext_of_subsingleton_primeQuotients
    {R : Type v} [CommRing R] [IsNoetherianRing R] [Small.{v} R]
    {N : ModuleCat.{v} R} [Module.Finite R (N : Type v)]
    {Y : ModuleCat.{v} R} {n : ℕ}
    [HasExt.{v} (ModuleCat.{v} R)]
    (h : ∀ P : Ideal R, P.IsPrime →
      ringKrullDim (R ⧸ P) ≤
        ringKrullDim (R ⧸ (⊤ : Submodule R (N : Type v)).annihilator) →
      Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) Y n)) :
    Subsingleton (Ext N Y n) := by
  obtain ⟨F⟩ := exists_primeFiltration (R := R) (M := (N : Type v))
  have hdev : ∀ j : Fin (F.k + 1),
      Subsingleton (Ext (ModuleCat.of R ((N : Type v) ⧸ F.K j)) Y n) := by
    intro j
    refine Fin.reverseInduction ?hlast ?hcast j
    · rw [F.htop]
      exact subsingleton_ext_quot_top Y n
    · intro i ih
      have ih' : Subsingleton
          (Ext (ModuleCat.of R ((N : Type v) ⧸ F.K i.succ)) Y n) := ih
      have hS : (LesSesPackages.submoduleSES
          ((F.K i.succ).map (F.K i.castSucc).mkQ)).ShortExact :=
        LesSesPackages.submoduleSES_shortExact _
      have hP : Subsingleton (Ext (ModuleCat.of R (R ⧸ F.P i)) Y n) :=
        h (F.P i) (F.hprime i) (factor_dim_le F i)
      obtain ⟨eFac⟩ := F.hfactor i
      have e₁base : ↥((F.K i.succ).map (F.K i.castSucc).mkQ)
          ≃ₗ[R] R ⧸ F.P i :=
        (mapMkQEquivQuotComap (F.K i.castSucc) (F.K i.succ)).trans eFac
      have h₁ : Subsingleton
          (Ext (LesSesPackages.submoduleSES
            ((F.K i.succ).map (F.K i.castSucc).mkQ)).X₁ Y n) :=
        subsingleton_ext_of_iso (LinearEquiv.toModuleIso e₁base).symm hP
      have e₃base : ((N : Type v) ⧸ F.K i.succ) ≃ₗ[R]
          (((N : Type v) ⧸ F.K i.castSucc) ⧸
            (F.K i.succ).map (F.K i.castSucc).mkQ) :=
        (Submodule.quotientQuotientEquivQuotient _ _ (F.hle i)).symm
      have h₃ : Subsingleton
          (Ext (LesSesPackages.submoduleSES
            ((F.K i.succ).map (F.K i.castSucc).mkQ)).X₃ Y n) :=
        subsingleton_ext_of_iso (LinearEquiv.toModuleIso e₃base) ih'
      exact LesSesPackages.subsingleton_ext_middle_of_subsingleton_ends hS Y n
        h₃ h₁
  have h0 := hdev 0
  rw [F.hbot] at h0
  have eBot : ((N : Type v) ⧸ (⊥ : Submodule R (N : Type v)))
      ≃ₗ[R] (N : Type v) := by
    have e := LinearMap.quotKerEquivOfSurjective
      (LinearMap.id : (N : Type v) →ₗ[R] (N : Type v))
      (fun x => ⟨x, rfl⟩)
    rw [LinearMap.ker_id] at e
    exact e
  exact subsingleton_ext_of_iso (LinearEquiv.toModuleIso eBot) h0

end AssociatedPrimes.PrimeFiltrationDevissage
