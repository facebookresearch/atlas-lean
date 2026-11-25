/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts.lean`,
`Definitions/Def_CerednikDrinfeld_SchemeNilpPoints.lean`,
`Theorems/Thm_RingHom_existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing.lean`,
`P2M/Sol/S_RingHom_existsUnique_forall_quotientMap_comp_eq_of_forall_smul_eq_of_isNoetherianRing.lean`,
`Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing.lean` and
`P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style. The algebra-functor and
nilpotent-points carriers are restated here in Mathlib style; the
auxiliary ring-homomorphism descent result is kept private to this file.
The statement is at universe level 0 throughout, as forced by its use of
`Scheme.{0}` and of points valued in commutative rings in `Type`.
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Finiteness.Basic

import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

/-!
# Nilpotent points factor through a finite quotient

For a scheme `X` with `f : X ⟶ Spec 𝒪`, `Scheme.pointsOver f : CommAlgCat 𝒪 ⥤ Type u` is its
functor of points over `Spec 𝒪`: a commutative `𝒪`-algebra `B` goes to the morphisms
`Spec B ⟶ X` over `Spec 𝒪`, covariantly in `B`. A morphism over `Spec 𝒪` induces a natural
transformation `Scheme.pointsOver.mapHom` between these functors.

The main theorem takes a finite group `G` acting on `M` over a Noetherian ring `𝒪`, and a
`G`-invariant morphism `p : M ⟶ X` over `Spec 𝒪` that is integral and affine, with `X` affine, `M`
and `X` locally of finite type over `𝒪`, `p` injective on global sections, and the global sections
of `X` mapping onto the `G`-invariant global sections of `M`. It shows that a `G`-invariant family
of maps from the points of `M` to the points of an affine `T` over `Spec 𝒪`, natural on the
`𝒪`-algebras in which a fixed `π : 𝒪` is nilpotent, factors uniquely through `p`.

## Main definitions

* `AlgebraicGeometry.Scheme.specOver`: the structure morphism `Spec B ⟶ Spec 𝒪` of an algebra.
* `AlgebraicGeometry.Scheme.pointsOver`: the functor of points over `Spec 𝒪`.
* `AlgebraicGeometry.Scheme.pointsOver.mapHom`: the natural transformation induced by a morphism
  over `Spec 𝒪`.

## Main results

* `Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing`

## Implementation notes

The proof works with global sections: the family gives a compatible tower of ring maps
`Γ(T, ⊤) → Γ(M, ⊤) ⧸ (π ^ n)`, which descends to `Γ(X, ⊤) ⧸ (π ^ n)` by the Artin–Rees lemma
applied to the `G`-invariants. The functor of points is universe-polymorphic; the theorem is stated
at universe 0.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

namespace AlgebraicGeometry

universe u

variable {𝒪 : Type u} [CommRing 𝒪]

/-- **Structure morphism of an algebra.** For a commutative `𝒪`-algebra `B`, the morphism
`Spec B ⟶ Spec 𝒪` induced by `algebraMap 𝒪 B`. -/
noncomputable abbrev Scheme.specOver (B : Type u) [CommRing B] [Algebra 𝒪 B] :
    Spec (.of B) ⟶ Spec (.of 𝒪) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))

theorem Scheme.specMap_algHom_comp_specOver {B : Type u} [CommRing B] [Algebra 𝒪 B]
    {B' : Type u} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B') :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver B' := by
  rw [Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_algebraMap]

/-- **Functor of points over a ring.** For `f : X ⟶ Spec 𝒪`, the functor from commutative
`𝒪`-algebras to types that sends `B` to the morphisms `Spec B ⟶ X` over `Spec 𝒪`. It is covariant
in `B`: a morphism `B ⟶ B'` acts by precomposition with `Spec B' ⟶ Spec B`. No condition is put on
`B`. -/
noncomputable def Scheme.pointsOver {X : Scheme.{u}} (f : X ⟶ Spec (.of 𝒪)) :
    CommAlgCat.{u} 𝒪 ⥤ Type u where
  obj B := { φ : Spec (.of B) ⟶ X // φ ≫ f = Scheme.specOver B }
  map g := TypeCat.ofHom fun φ => ⟨Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ φ.1, by
    rw [Category.assoc, φ.2, Scheme.specMap_algHom_comp_specOver]⟩
  map_id B := by
    ext φ
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ φ.1 = φ.1
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  map_comp g h := by
    ext φ
    show Spec.map (CommRingCat.ofHom ((h.hom.comp g.hom).toRingHom)) ≫ φ.1 =
      Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ φ.1)
    simp only [AlgHom.toRingHom_eq_coe]
    rw [AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

@[simp] theorem Scheme.pointsOver_map_val {X : Scheme.{u}} (f : X ⟶ Spec (.of 𝒪))
    {B B' : CommAlgCat.{u} 𝒪} (g : B ⟶ B') (φ : (Scheme.pointsOver f).obj B) :
    ((Scheme.pointsOver f).map g φ).1 = Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ φ.1 :=
  rfl

/-- **Map of points over a ring.** A morphism `h : X ⟶ Y` over `Spec 𝒪` induces the natural
transformation `pointsOver fX ⟶ pointsOver fY` that composes each point with `h`. -/
noncomputable def Scheme.pointsOver.mapHom {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of 𝒪))
    (fY : Y ⟶ Spec (.of 𝒪)) (h : X ⟶ Y) (w : h ≫ fY = fX) :
    Scheme.pointsOver fX ⟶ Scheme.pointsOver fY where
  app B := TypeCat.ofHom fun φ => ⟨φ.1 ≫ h, by rw [Category.assoc, w, φ.2]⟩
  naturality B B' g := by
    ext φ
    apply Subtype.ext
    show (Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ φ.1) ≫ h =
      Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ (φ.1 ≫ h)
    rw [Category.assoc]

@[simp] theorem Scheme.pointsOver.mapHom_app_val {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of 𝒪))
    (fY : Y ⟶ Spec (.of 𝒪)) (h : X ⟶ Y) (w : h ≫ fY = fX) {B : CommAlgCat.{u} 𝒪}
    (φ : (Scheme.pointsOver fX).obj B) :
    ((Scheme.pointsOver.mapHom fX fY h w).app B φ).1 = φ.1 ≫ h :=
  rfl

end AlgebraicGeometry

namespace FormalInvFactor29

open Pointwise

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

private theorem mem_span_pow_iff (π : R) (N : ℕ) (x : A) :
    x ∈ Ideal.span {algebraMap R A π ^ N} ↔ x ∈ ((Ideal.span {π}) ^ N • ⊤ : Submodule R A) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, Submodule.mem_top, by rw [Algebra.smul_def, map_pow, mul_comm]⟩
  · rintro ⟨a, -, rfl⟩
    exact ⟨a, by rw [Algebra.smul_def, map_pow, mul_comm]⟩

private theorem mem_span_pow_iff_self (π : R) (N : ℕ) (r : R) :
    r ∈ Ideal.span {π ^ N} ↔ r ∈ ((Ideal.span {π}) ^ N • ⊤ : Submodule R R) := by
  have := mem_span_pow_iff (R := R) (A := R) π N r
  rwa [show algebraMap R R π = π from rfl] at this

private theorem mem_pow_smul_map_iff {M P : Type} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (I : Ideal R) (N : ℕ) (f : M →ₗ[R] P) (y : P) :
    y ∈ (I ^ N • LinearMap.range f : Submodule R P) → ∃ m ∈ (I ^ N • ⊤ : Submodule R M), f m = y := by
  intro hy
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at hy
  obtain ⟨m, hm, rfl⟩ := hy
  exact ⟨m, hm, rfl⟩

section Shifts

variable (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]

private def delta : A →ₗ[R] (G → A) where
  toFun a := fun g => g • a - a
  map_add' a b := by ext g; simp [smul_add]; abel
  map_smul' r a := by ext g; simp [smul_sub, smul_comm]

private theorem delta_apply (a : A) (g : G) : delta (R := R) G a g = g • a - a := rfl

private theorem delta_eq_zero_iff (a : A) : delta (R := R) G a = 0 ↔ ∀ g : G, g • a = a := by
  constructor
  · intro h g
    have := congrFun h g
    rw [delta_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  · intro h
    ext g
    rw [delta_apply, h g, sub_self, Pi.zero_apply]

private theorem pi_mem_smul_top (π : R) (m : ℕ) (f : G → A)
    (h : ∀ g : G, f g ∈ ((Ideal.span {π}) ^ m • ⊤ : Submodule R A)) :
    f ∈ ((Ideal.span {π}) ^ m • ⊤ : Submodule R (G → A)) := by
  simp_rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  choose b _hb hb using h
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨b, Submodule.mem_top, funext fun g => by rw [Pi.smul_apply, hb g]⟩

private theorem exists_shift_invariant [IsNoetherianRing R] [Module.Finite R A]
    (hinv : ∀ a : A, (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap R A)) (π : R) :
    ∃ k : ℕ, ∀ (N : ℕ) (a : A), (∀ g : G, g • a - a ∈ Ideal.span {algebraMap R A π ^ (N + k)}) →
      ∃ r : R, a - algebraMap R A r ∈ Ideal.span {algebraMap R A π ^ N} := by
  classical
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {π})
    (LinearMap.range (delta (R := R) G) : Submodule R (G → A))
  refine ⟨k, fun N a ha => ?_⟩
  have hδ : delta (R := R) G a ∈ ((Ideal.span {π}) ^ (N + k) • ⊤ : Submodule R (G → A)) :=
    pi_mem_smul_top G π (N + k) _ (fun g => (mem_span_pow_iff π (N + k) _).mp (by rw [delta_apply]; exact ha g))
  have hmem : delta (R := R) G a ∈
      ((Ideal.span {π}) ^ (N + k) • ⊤ ⊓ LinearMap.range (delta (R := R) G) : Submodule R (G → A)) :=
    ⟨hδ, LinearMap.mem_range_self _ a⟩
  have hk' := hk (N + k) (Nat.le_add_left k N)
  rw [Nat.add_sub_cancel] at hk'
  rw [hk'] at hmem
  have hmem' : delta (R := R) G a ∈ ((Ideal.span {π}) ^ N • LinearMap.range (delta (R := R) G) : Submodule R (G → A)) :=
    Submodule.smul_mono le_rfl inf_le_right hmem
  obtain ⟨a', ha', hfa'⟩ :
      ∃ m ∈ ((Ideal.span {π}) ^ N • ⊤ : Submodule R A), delta (R := R) G m = delta (R := R) G a :=
    mem_pow_smul_map_iff (M := A) (P := G → A) (Ideal.span {π}) N (delta (R := R) G) (delta (R := R) G a) hmem'
  have hinv' : ∀ g : G, g • (a - a') = a - a' := by
    rw [← delta_eq_zero_iff (R := R) G, map_sub, hfa', sub_self]
  obtain ⟨r, hr⟩ := hinv _ hinv'
  refine ⟨r, ?_⟩
  rw [hr, sub_sub_cancel]
  exact (mem_span_pow_iff π N a').mpr ha'

private theorem exists_shift_base [IsNoetherianRing R] [Module.Finite R A] (hinj : Function.Injective (algebraMap R A)) (π : R) :
    ∃ k : ℕ, ∀ (N : ℕ) (r : R), algebraMap R A r ∈ Ideal.span {algebraMap R A π ^ (N + k)} → r ∈ Ideal.span {π ^ N} := by
  classical
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (Ideal.span {π})
    (LinearMap.range (Algebra.linearMap R A) : Submodule R A)
  refine ⟨k, fun N r hr => ?_⟩
  have hmem : algebraMap R A r ∈
      ((Ideal.span {π}) ^ (N + k) • ⊤ ⊓ LinearMap.range (Algebra.linearMap R A) : Submodule R A) :=
    ⟨(mem_span_pow_iff π (N + k) _).mp hr, LinearMap.mem_range_self (Algebra.linearMap R A) r⟩
  have hk' := hk (N + k) (Nat.le_add_left k N)
  rw [Nat.add_sub_cancel] at hk'
  rw [hk'] at hmem
  have hmem' : algebraMap R A r ∈ ((Ideal.span {π}) ^ N • LinearMap.range (Algebra.linearMap R A) : Submodule R A) :=
    Submodule.smul_mono le_rfl inf_le_right hmem
  obtain ⟨r', hr', hfr'⟩ := mem_pow_smul_map_iff (Ideal.span {π}) N (Algebra.linearMap R A) _ hmem'
  have : r' = r := hinj hfr'
  subst this
  exact (mem_span_pow_iff_self π N r').mpr hr'

end Shifts

private theorem lift_down {A C : Type} [CommRing A] [CommRing C] (x : A)
    (q : ∀ n : ℕ, C →+* A ⧸ Ideal.span {x ^ n})
    (hq : ∀ n : ℕ, (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow x (Nat.le_succ n)))).comp (q (n + 1)) = q n)
    (d n : ℕ) (a : A) (z : C) (h : Ideal.Quotient.mk (Ideal.span {x ^ (n + d)}) a = q (n + d) z) :
    Ideal.Quotient.mk (Ideal.span {x ^ n}) a = q n z := by
  induction d generalizing n with
  | zero => simpa using h
  | succ d ih =>
    apply ih
    have h' : Ideal.Quotient.mk (Ideal.span {x ^ (n + d + 1)}) a = q (n + d + 1) z := by
      rw [show n + d + 1 = n + (d + 1) by ring]; exact h
    rw [← hq (n + d), RingHom.comp_apply, ← h', Ideal.Quotient.factor_mk]

private theorem span_pow_le {A : Type} [CommRing A] (x : A) {n m : ℕ} (h : n ≤ m) :
    Ideal.span {x ^ m} ≤ Ideal.span {x ^ n} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow x h)



open FormalInvFactor29

private theorem ringHom_existsUnique_aux
    (R A C : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing C]
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
    (hinj : Function.Injective (algebraMap R A))
    (hinv : ∀ a : A, (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap R A))
    (π : R)
    (c : ∀ n : ℕ, C →+* A ⧸ Ideal.span {algebraMap R A π ^ n})
    (hc : ∀ n : ℕ, (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap R A π) (Nat.le_succ n)))).comp (c (n + 1)) = c n)
    (hG : ∀ (n : ℕ) (g : G) (z : C) (a : A), Ideal.Quotient.mk _ a = c n z →
        Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ n}) (g • a) = c n z) :
    ∃! d : ∀ n : ℕ, C →+* R ⧸ Ideal.span {π ^ n},
      (∀ n : ℕ, (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ n)))).comp (d (n + 1)) = d n) ∧
      (∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap R A π ^ n}) (algebraMap R A)
          (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d n) = c n) := by
  classical
  obtain ⟨k, hk⟩ := exists_shift_invariant (R := R) G hinv π
  obtain ⟨k', hk'⟩ := exists_shift_base (R := R) (A := A) hinj π

  let M : ℕ → ℕ := fun n => n + k' + k
  let Approx : ℕ → C → R → Prop := fun n z r =>
    ∃ a : A, Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ M n}) a = c (M n) z ∧ a - algebraMap R A r ∈ Ideal.span {algebraMap R A π ^ (n + k')}

  have hE : ∀ n z, ∃ r, Approx n z r := by
    intro n z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (c (M n) z)
    have hga : ∀ g : G, g • a - a ∈ Ideal.span {algebraMap R A π ^ (n + k' + k)} := by
      intro g
      rw [← Ideal.Quotient.eq, ha]
      exact hG (M n) g z a ha
    obtain ⟨r, hr⟩ := hk (n + k') a hga
    exact ⟨r, a, ha, hr⟩

  have hlifts : ∀ (n : ℕ) (z : C) (a a' : A), Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ M n}) a = c (M n) z →
      Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ M n}) a' = c (M n) z → a - a' ∈ Ideal.span {algebraMap R A π ^ (n + k')} := by
    intro n z a a' ha ha'
    have : a - a' ∈ Ideal.span {algebraMap R A π ^ M n} := by rw [← Ideal.Quotient.eq, ha, ha']
    exact span_pow_le (algebraMap R A π) (by show n + k' ≤ n + k' + k; omega) this

  have hU : ∀ n z r r', Approx n z r → Approx n z r' →
      Ideal.Quotient.mk (Ideal.span {π ^ n}) r = Ideal.Quotient.mk (Ideal.span {π ^ n}) r' := by
    intro n z r r' ⟨a, ha, har⟩ ⟨a', ha', har'⟩
    rw [Ideal.Quotient.eq]
    apply hk' n
    rw [map_sub]
    have : algebraMap R A r - algebraMap R A r' = (a' - algebraMap R A r') - (a' - a) - (a - algebraMap R A r) := by ring
    rw [this]
    exact sub_mem (sub_mem har' (hlifts n z a' a ha' ha)) har

  have hMul : ∀ n z z' r r', Approx n z r → Approx n z' r' → Approx n (z * z') (r * r') := by
    intro n z z' r r' ⟨a, ha, har⟩ ⟨a', ha', har'⟩
    refine ⟨a * a', by rw [map_mul, map_mul, ha, ha'], ?_⟩
    have : a * a' - algebraMap R A (r * r') = a * (a' - algebraMap R A r') + (a - algebraMap R A r) * algebraMap R A r' := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ har') (Ideal.mul_mem_right _ _ har)
  have hAdd : ∀ n z z' r r', Approx n z r → Approx n z' r' → Approx n (z + z') (r + r') := by
    intro n z z' r r' ⟨a, ha, har⟩ ⟨a', ha', har'⟩
    refine ⟨a + a', by rw [map_add, map_add, ha, ha'], ?_⟩
    have : a + a' - algebraMap R A (r + r') = (a - algebraMap R A r) + (a' - algebraMap R A r') := by rw [map_add]; ring
    rw [this]
    exact add_mem har har'
  have hOne : ∀ n, Approx n 1 1 := fun n => ⟨1, by rw [map_one, map_one], by rw [map_one, sub_self]; exact zero_mem _⟩
  have hZero : ∀ n, Approx n 0 0 := fun n => ⟨0, by rw [map_zero, map_zero], by rw [map_zero, sub_self]; exact zero_mem _⟩

  have hDown : ∀ n z r, Approx (n + 1) z r → Approx n z r := by
    intro n z r ⟨a, ha, har⟩
    refine ⟨a, ?_, span_pow_le (algebraMap R A π) (by omega) har⟩

    have hMn : M (n + 1) = M n + 1 := by show n + 1 + k' + k = n + k' + k + 1; ring
    have ha' : Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ (M n + 1)}) a = c (M n + 1) z := by rw [← hMn]; exact ha
    exact lift_down (algebraMap R A π) c hc 1 (M n) a z ha'

  let d : ∀ n : ℕ, C →+* R ⧸ Ideal.span {π ^ n} := fun n =>
    { toFun := fun z => Ideal.Quotient.mk _ (hE n z).choose
      map_one' := by rw [hU n 1 _ 1 (hE n 1).choose_spec (hOne n), map_one]
      map_mul' := fun z z' => by
        rw [hU n (z * z') _ _ (hE n (z * z')).choose_spec (hMul n z z' _ _ (hE n z).choose_spec (hE n z').choose_spec), map_mul]
      map_zero' := by rw [hU n 0 _ 0 (hE n 0).choose_spec (hZero n), map_zero]
      map_add' := fun z z' => by
        rw [hU n (z + z') _ _ (hE n (z + z')).choose_spec (hAdd n z z' _ _ (hE n z).choose_spec (hE n z').choose_spec), map_add] }
  have hd : ∀ n z r, Approx n z r → d n z = Ideal.Quotient.mk _ r := fun n z r h =>
    hU n z _ r (hE n z).choose_spec h

  have hdcompat : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ n)))).comp (d (n + 1)) = d n := by
    intro n
    apply RingHom.ext
    intro z
    rw [RingHom.comp_apply, hd (n + 1) z _ (hE (n + 1) z).choose_spec, Ideal.Quotient.factor_mk,
      hd n z _ (hDown n z _ (hE (n + 1) z).choose_spec)]
  have hdfac : ∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap R A π ^ n}) (algebraMap R A)
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d n) = c n := by
    intro n
    apply RingHom.ext
    intro z
    obtain ⟨a, ha, har⟩ := (hE n z).choose_spec
    rw [RingHom.comp_apply, hd n z _ ⟨a, ha, har⟩, Ideal.quotientMap_mk]
    have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ n}) a = c n z :=
      lift_down (algebraMap R A π) c hc (k' + k) n a z (by rw [show n + (k' + k) = M n from (Nat.add_assoc _ _ _).symm]; exact ha)
    rw [← h1, Ideal.Quotient.eq]
    have : algebraMap R A (hE n z).choose - a = -(a - algebraMap R A (hE n z).choose) := by ring
    rw [this]
    exact neg_mem (span_pow_le (algebraMap R A π) (by omega) har)
  refine ⟨d, ⟨hdcompat, hdfac⟩, ?_⟩

  rintro d' ⟨hd'compat, hd'fac⟩
  funext n
  apply RingHom.ext
  intro z

  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (d' (n + k') z)

  have hd'n : d' n z = Ideal.Quotient.mk _ s := by
    have := lift_down (A := R) (C := C) π d' hd'compat k' n s z hs
    exact this.symm

  obtain ⟨a, ha, har⟩ := (hE n z).choose_spec
  rw [hd'n, hd n z _ ⟨a, ha, har⟩, Ideal.Quotient.eq]
  apply hk' n

  have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ (n + k')}) (algebraMap R A s) = c (n + k') z := by
    have := congrArg (fun f : C →+* A ⧸ Ideal.span {algebraMap R A π ^ (n + k')} => f z) (hd'fac (n + k'))
    simp only [RingHom.comp_apply] at this
    rw [← hs, Ideal.quotientMap_mk] at this
    exact this
  have h2 : Ideal.Quotient.mk (Ideal.span {algebraMap R A π ^ (n + k')}) a = c (n + k') z :=
    lift_down (algebraMap R A π) c hc k (n + k') a z (by exact ha)
  have h3 : algebraMap R A s - a ∈ Ideal.span {algebraMap R A π ^ (n + k')} := by rw [← Ideal.Quotient.eq, h1, h2]
  rw [map_sub]
  have : algebraMap R A s - algebraMap R A ((hE n z).choose) = (algebraMap R A s - a) + (a - algebraMap R A (hE n z).choose) := by ring
  rw [this]
  exact add_mem h3 har

namespace SchemeNilpFactor

variable {𝒪 : Type} [CommRing 𝒪]

section Dictionary

variable {M : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪))

private noncomputable def baseHom : 𝒪 →+* Γ(M, ⊤) :=
  fM.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom

private noncomputable def toHom {B : Type} [CommRing B] (φ : Spec (CommRingCat.of B) ⟶ M) : Γ(M, ⊤) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp φ.appTop.hom

private theorem ΓSpecIso_inv_hom_apply (R : Type) [CommRing R] (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom r = r
  rw [Iso.inv_hom_id]; rfl

private theorem ΓSpecIso_hom_inv_apply (R : Type) [CommRing R] (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r = r
  rw [Iso.hom_inv_id]; rfl

private theorem ΓSpecIso_nat_apply {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom r) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have h := congrArg (fun g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of S => g.hom r) this
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

private theorem toHom_comp_baseHom {B : Type} [CommRing B] [Algebra 𝒪 B] (φ : Spec (CommRingCat.of B) ⟶ M)
    (hφ : φ ≫ fM = Scheme.specOver B) : (toHom φ).comp (baseHom fM) = algebraMap 𝒪 B := by
  apply RingHom.ext
  intro o
  show (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.appTop.hom (fM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom o))) =
    algebraMap 𝒪 B o
  have h1 : φ.appTop.hom (fM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom o)) =
      (Scheme.specOver (𝒪 := 𝒪) B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv.hom o) := by
    rw [← hφ, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [h1, Scheme.specOver, ΓSpecIso_nat_apply, ΓSpecIso_inv_hom_apply]

private noncomputable def ofHom [IsAffine M] {B : Type} [CommRing B] (ξ : Γ(M, ⊤) →+* B) : Spec (CommRingCat.of B) ⟶ M :=
  Spec.map (CommRingCat.ofHom ξ) ≫ M.isoSpec.inv

private theorem ofHom_toHom [IsAffine M] {B : Type} [CommRing B] (φ : Spec (CommRingCat.of B) ⟶ M) : ofHom (toHom φ) = φ := by
  unfold ofHom toHom
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    Category.assoc, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv,
    Category.comp_id]

private theorem toHom_ofHom [IsAffine M] {B : Type} [CommRing B] (ξ : Γ(M, ⊤) →+* B) : toHom (ofHom ξ) = ξ := by
  unfold ofHom toHom
  apply RingHom.ext
  intro a
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, ΓSpecIso_nat_apply]
  congr 1

  have h1 : M.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(M, ⊤)).hom := by rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  have h2 : M.isoSpec.hom.appTop ≫ M.isoSpec.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]; simp
  have h3 : M.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(M, ⊤)).hom = 𝟙 _ := by
    rw [← h1, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]; simp
  have := congrArg (fun g : Γ(M, ⊤) ⟶ Γ(M, ⊤) => g.hom a) h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  exact this

private theorem isoSpec_inv_comp [IsAffine M] :
    M.isoSpec.inv ≫ fM = Spec.map (CommRingCat.ofHom (baseHom fM)) := by
  have h1 : fM = M.toSpecΓ ≫ Spec.map fM.appTop ≫ (Spec (CommRingCat.of 𝒪)).isoSpec.inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have h2 : (Spec (CommRingCat.of 𝒪)).isoSpec.inv = Spec.map (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).inv :=
    Scheme.isoSpec_Spec_inv _
  rw [Iso.inv_comp_eq, Scheme.isoSpec_hom]
  conv_lhs => rw [h1]
  rw [h2, ← Spec.map_comp, baseHom, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom]

private theorem ofHom_over [IsAffine M] {B : Type} [CommRing B] [Algebra 𝒪 B] (ξ : Γ(M, ⊤) →+* B)
    (hξ : ξ.comp (baseHom fM) = algebraMap 𝒪 B) : ofHom ξ ≫ fM = Scheme.specOver B := by
  unfold ofHom
  rw [Category.assoc, isoSpec_inv_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hξ]

end Dictionary

section Action

variable {M : Scheme.{0}} {G : Type} [Group G] (ρ : G →* Aut M)

private noncomputable def sectionsAction : MulSemiringAction G Γ(M, ⊤) where
  smul g a := (ρ g⁻¹).asIso.hom.appTop.hom a
  one_smul a := by
    show (ρ 1⁻¹).asIso.hom.appTop.hom a = a
    rw [inv_one, map_one]
    show (𝟙 M : M ⟶ M).appTop.hom a = a
    simp
  mul_smul g h a := by
    show (ρ (g * h)⁻¹).asIso.hom.appTop.hom a = (ρ g⁻¹).asIso.hom.appTop.hom ((ρ h⁻¹).asIso.hom.appTop.hom a)
    rw [mul_inv_rev, map_mul, Aut.mul_asIso, Iso.trans_hom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_apply]
  smul_zero g := map_zero _
  smul_add g a b := map_add _ a b
  smul_one g := map_one _
  smul_mul g a b := map_mul _ a b

private theorem sectionsAction_smul (g : G) (a : Γ(M, ⊤)) :
    (letI := sectionsAction ρ; g • a) = (ρ g⁻¹).asIso.hom.appTop.hom a := rfl

private theorem ofHom_comp_hom [IsAffine M] {B : Type} [CommRing B] (ξ : Γ(M, ⊤) →+* B) (h : M ⟶ M) :
    ofHom ξ ≫ h = ofHom (ξ.comp h.appTop.hom) := by
  unfold ofHom
  have hnat : h = M.isoSpec.hom ≫ Spec.map h.appTop ≫ M.isoSpec.inv := by
    rw [Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  conv_lhs => rw [hnat]
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, ← Spec.map_comp, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom]

end Action

section Points

variable {M : Scheme.{0}} [IsAffine M]

private theorem specMap_comp_ofHom {B B' : Type} [CommRing B] [CommRing B'] (ξ : Γ(M, ⊤) →+* B) (φ : B →+* B') :
    Spec.map (CommRingCat.ofHom φ) ≫ ofHom ξ = ofHom (φ.comp ξ) := by
  unfold ofHom
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem toHom_specMap_comp {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') (x : Spec (CommRingCat.of B) ⟶ M) :
    toHom (Spec.map (CommRingCat.ofHom φ) ≫ x) = φ.comp (toHom x) := by
  conv_lhs => rw [← ofHom_toHom x, specMap_comp_ofHom]
  rw [toHom_ofHom]

private theorem toHom_comp {Y : Scheme.{0}} {B : Type} [CommRing B] (x : Spec (CommRingCat.of B) ⟶ M) (h : M ⟶ Y) :
    toHom (x ≫ h) = (toHom x).comp h.appTop.hom := by
  unfold toHom
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc]

end Points

section Ev

variable {X T : Scheme.{0}} [IsAffine T] (f : X ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪))
  {ϖ : Γ(X, ⊤)} (d : ∀ n : ℕ, Γ(T, ⊤) →+* Γ(X, ⊤) ⧸ Ideal.span {ϖ ^ n})

private noncomputable def evHom {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) : Γ(T, ⊤) →+* B :=
  (Ideal.Quotient.lift _ η hN).comp (d N)

private theorem kill_mono (ϖ : Γ(X, ⊤)) {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N j : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) : ∀ a ∈ Ideal.span {ϖ ^ (N + j)}, η a = 0 :=
  fun a ha => hN a (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_add_right N j)) ha)

private theorem kill_of_pow_eq_zero {B : Type} [CommRing B] [Algebra 𝒪 B] (π : 𝒪) (η : Γ(X, ⊤) →+* B)
    (hη : η.comp (baseHom f) = algebraMap 𝒪 B) (N : ℕ) (hN : algebraMap 𝒪 B π ^ N = 0) :
    ∀ a ∈ Ideal.span {baseHom f π ^ N}, η a = 0 := by
  intro a ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_pow, show η (baseHom f π) = algebraMap 𝒪 B π from by rw [← hη]; rfl, hN, mul_zero]

variable (hdc : ∀ n : ℕ, (Ideal.Quotient.factor
    (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n)))).comp (d (n + 1)) = d n)

include hdc in
private theorem evHom_add {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N j : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (hNj : ∀ a ∈ Ideal.span {ϖ ^ (N + j)}, η a = 0) :
    evHom d η N hN = evHom d η (N + j) hNj := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [ih (kill_mono ϖ η N j hN), evHom, evHom, ← hdc (N + j), ← RingHom.comp_assoc]
    congr 1
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

include hdc in
private theorem evHom_indep {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N N' : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (hN' : ∀ a ∈ Ideal.span {ϖ ^ N'}, η a = 0) :
    evHom d η N hN = evHom d η N' hN' := by
  rw [evHom_add d hdc η N N' hN (kill_mono ϖ η N N' hN), evHom_add d hdc η N' N hN' (kill_mono ϖ η N' N hN')]
  suffices key : ∀ (m m' : ℕ) (_ : m = m') (h : ∀ a ∈ Ideal.span {ϖ ^ m}, η a = 0)
      (h' : ∀ a ∈ Ideal.span {ϖ ^ m'}, η a = 0), evHom d η m h = evHom d η m' h' from
    key _ _ (Nat.add_comm N N') _ _
  rintro m _ rfl h h'
  rfl

private theorem evHom_congr {B : Type} [CommRing B] {η η' : Γ(X, ⊤) →+* B} (e : η = η') (N : ℕ)
    (h : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (h' : ∀ a ∈ Ideal.span {ϖ ^ N}, η' a = 0) :
    evHom d η N h = evHom d η' N h' := by
  subst e; rfl

private theorem comp_evHom {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') (η : Γ(X, ⊤) →+* B) (N : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) (hN' : ∀ a ∈ Ideal.span {ϖ ^ N}, φ.comp η a = 0) :
    φ.comp (evHom d η N hN) = evHom d (φ.comp η) N hN' := by
  rw [evHom, evHom, ← RingHom.comp_assoc]
  congr 1
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk]

private theorem evHom_comp_baseHom (hdO : ∀ (n : ℕ) (o : 𝒪), d n (baseHom t o) = Ideal.Quotient.mk _ (baseHom f o))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (η : Γ(X, ⊤) →+* B) (hη : η.comp (baseHom f) = algebraMap 𝒪 B)
    (N : ℕ) (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) : (evHom d η N hN).comp (baseHom t) = algebraMap 𝒪 B := by
  apply RingHom.ext
  intro o
  rw [← hη, evHom, RingHom.comp_apply, RingHom.comp_apply, hdO, Ideal.Quotient.lift_mk, RingHom.comp_apply]

private theorem lift_comp_quotientMap {A B : Type} [CommRing A] [CommRing B] (ι : Γ(X, ⊤) →+* A) (ξ : A →+* B) (N : ℕ)
    (hξ : ∀ a ∈ Ideal.span {ι ϖ ^ N}, ξ a = 0) (hη : ∀ a ∈ Ideal.span {ϖ ^ N}, ξ.comp ι a = 0) :
    (Ideal.Quotient.lift _ ξ hξ).comp (Ideal.quotientMap (Ideal.span {ι ϖ ^ N}) ι
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)) =
    Ideal.Quotient.lift _ (ξ.comp ι) hη := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]

end Ev

section Tower

variable {Y T : Scheme.{0}} [IsAffine Y] [IsAffine T] (fY : Y ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪))
  (π : 𝒪)

private noncomputable def canPt (a : Γ(Y, ⊤)) (n : ℕ) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    (Scheme.pointsOver fY).obj (.of 𝒪 (Γ(Y, ⊤) ⧸ Ideal.span {a ^ n})) :=
  letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
  ⟨ofHom (Ideal.Quotient.mk _), ofHom_over fY _ rfl⟩

private theorem canPt_val (a : Γ(Y, ⊤)) (n : ℕ) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    (canPt fY a n).1 = ofHom (Ideal.Quotient.mk (Ideal.span {a ^ n})) := rfl

variable (v : ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) →
    (Scheme.pointsOver fY).obj B → (Scheme.pointsOver t).obj B)
  (hv_nat : ∀ (B B' : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B') (x : (Scheme.pointsOver fY).obj B),
    v B' hB' ((Scheme.pointsOver fY).map φ x) = (Scheme.pointsOver t).map φ (v B hB x))

include hv_nat in

private theorem tower_compat (a : Γ(Y, ⊤)) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    ∀ (hBn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(Y, ⊤) ⧸ Ideal.span {a ^ n}) π)) (n : ℕ),
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ n)))).comp
        (toHom (v _ (hBn (n + 1)) (canPt fY a (n + 1))).1) = toHom (v _ (hBn n) (canPt fY a n)).1 := by
  intro hBn n
  letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
  let φn : (Γ(Y, ⊤) ⧸ Ideal.span {a ^ (n + 1)}) →ₐ[𝒪] (Γ(Y, ⊤) ⧸ Ideal.span {a ^ n}) :=
    Ideal.Quotient.factorₐ 𝒪 (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ n)))
  have hφn : φn.toRingHom = Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a (Nat.le_succ n))) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  have hpt : (Scheme.pointsOver fY).map (CommAlgCat.ofHom φn) (canPt fY a (n + 1)) =
      canPt fY a n := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom φn.toRingHom) ≫ ofHom (Ideal.Quotient.mk _) = ofHom (Ideal.Quotient.mk _)
    rw [specMap_comp_ofHom]
    congr 1
  have hz := hv_nat _ _ (hBn (n + 1)) (hBn n) (CommAlgCat.ofHom φn) (canPt fY a (n + 1))
  rw [hpt] at hz
  rw [hz, ← hφn]
  exact (toHom_specMap_comp φn.toRingHom _).symm

private theorem eq_map_canPt (a : Γ(Y, ⊤)) {B : CommAlgCat.{0} 𝒪}
    (y : (Scheme.pointsOver fY).obj B) (N : ℕ)
    (hN : ∀ a' ∈ Ideal.span {a ^ N}, toHom y.1 a' = 0) :
    letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
    ∃ ξN : CommAlgCat.of 𝒪 (Γ(Y, ⊤) ⧸ Ideal.span {a ^ N}) ⟶ B,
      ξN.hom.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {a ^ N})) = toHom y.1 ∧
        y = (Scheme.pointsOver fY).map ξN (canPt fY a N) := by
  letI : Algebra 𝒪 Γ(Y, ⊤) := (baseHom fY).toAlgebra
  have hξ : (toHom y.1).comp (baseHom fY) = algebraMap 𝒪 B := toHom_comp_baseHom fY y.1 y.2
  let ξN : CommAlgCat.of 𝒪 (Γ(Y, ⊤) ⧸ Ideal.span {a ^ N}) ⟶ B := CommAlgCat.ofHom
    (Ideal.Quotient.liftₐ _ (AlgHom.mk (toHom y.1) (fun o => by rw [← hξ]; rfl)) hN)
  have hξN : ξN.hom.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {a ^ N})) = toHom y.1 :=
    RingHom.ext fun _ => rfl
  refine ⟨ξN, hξN, Subtype.ext ?_⟩
  show y.1 = Spec.map (CommRingCat.ofHom ξN.hom.toRingHom) ≫ ofHom (Ideal.Quotient.mk _)
  rw [specMap_comp_ofHom, hξN]
  exact (ofHom_toHom y.1).symm

end Tower

section Invariance

variable {M T : Scheme.{0}} [IsAffine M] [IsAffine T] (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪))
  (π : 𝒪) {G : Type} [Group G] (ρ : G →* Aut M) (hover : ∀ g : G, (ρ g).asIso.hom ≫ fM = fM)
  (u : ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) →
    (Scheme.pointsOver fM).obj B → (Scheme.pointsOver t).obj B)
  (hu_nat : ∀ (B B' : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B') (x : (Scheme.pointsOver fM).obj B),
    u B' hB' ((Scheme.pointsOver fM).map φ x) = (Scheme.pointsOver t).map φ (u B hB x))
  (hu_inv : ∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G)
    (y : (Scheme.pointsOver fM).obj B),
    u B hB ((Scheme.pointsOver.mapHom fM fM (ρ g).asIso.hom (hover g)).app B y) = u B hB y)

include hu_nat hu_inv in

private theorem tower_invariant (a : Γ(M, ⊤)) (ha : ∀ g : G, (ρ g).asIso.hom.appTop.hom a = a)
    (hcomm : ∀ (g : G) (o : 𝒪), (ρ g).asIso.hom.appTop.hom (baseHom fM o) = baseHom fM o) :
    letI : Algebra 𝒪 Γ(M, ⊤) := (baseHom fM).toAlgebra
    ∀ (hBn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(M, ⊤) ⧸ Ideal.span {a ^ n}) π)) (n : ℕ) (g : G)
      (zC : Γ(T, ⊤)) (b : Γ(M, ⊤)),
      Ideal.Quotient.mk _ b = toHom (u _ (hBn n) (canPt fM a n)).1 zC →
      Ideal.Quotient.mk (Ideal.span {a ^ n}) ((ρ g).asIso.hom.appTop.hom b) = toHom (u _ (hBn n) (canPt fM a n)).1 zC := by
  intro hBn n g zC b hb
  letI : Algebra 𝒪 Γ(M, ⊤) := (baseHom fM).toAlgebra
  let σ : Γ(M, ⊤) →ₐ[𝒪] Γ(M, ⊤) := AlgHom.mk (ρ g).asIso.hom.appTop.hom (hcomm g)
  have hσI : Ideal.span {a ^ n} ≤ (Ideal.span {a ^ n}).comap σ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    show (ρ g).asIso.hom.appTop.hom (a ^ n) ∈ Ideal.span {a ^ n}
    rw [map_pow, ha]
    exact Ideal.subset_span rfl
  let gbar : (Γ(M, ⊤) ⧸ Ideal.span {a ^ n}) →ₐ[𝒪] (Γ(M, ⊤) ⧸ Ideal.span {a ^ n}) := Ideal.quotientMapₐ _ σ hσI
  have hpt : (Scheme.pointsOver fM).map (CommAlgCat.ofHom gbar) (canPt fM a n) =
      (Scheme.pointsOver.mapHom fM fM (ρ g).asIso.hom (hover g)).app _ (canPt fM a n) := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom gbar.toRingHom) ≫ ofHom (Ideal.Quotient.mk _) = ofHom (Ideal.Quotient.mk _) ≫ (ρ g).asIso.hom
    rw [specMap_comp_ofHom, ofHom_comp_hom]
    congr 1
  have hz : (Scheme.pointsOver t).map (CommAlgCat.ofHom gbar) (u _ (hBn n) (canPt fM a n)) =
      u _ (hBn n) (canPt fM a n) := by
    rw [← hu_nat _ _ (hBn n) (hBn n) (CommAlgCat.ofHom gbar) (canPt fM a n), hpt]
    exact hu_inv _ (hBn n) g (canPt fM a n)
  have hcg : gbar.toRingHom.comp (toHom (u _ (hBn n) (canPt fM a n)).1) = toHom (u _ (hBn n) (canPt fM a n)).1 := by
    conv_rhs => rw [← hz]
    exact (toHom_specMap_comp gbar.toRingHom _).symm
  rw [← hcg, RingHom.comp_apply, ← hb]
  rfl

end Invariance

section Compat

private theorem descent_comp_eq {𝒪 R A C : Type} [CommRing 𝒪] [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [CommRing C] (G : Type) [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
    (hinj : Function.Injective (algebraMap R A))
    (hinv : ∀ a : A, (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap R A)) (ϖ : R)
    (c : ∀ n : ℕ, C →+* A ⧸ Ideal.span {algebraMap R A ϖ ^ n})
    (hc : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap R A ϖ) (Nat.le_succ n)))).comp (c (n + 1)) = c n)
    (hG : ∀ (n : ℕ) (g : G) (z : C) (a : A), Ideal.Quotient.mk _ a = c n z →
      Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ ^ n}) (g • a) = c n z)
    (d : ∀ n : ℕ, C →+* R ⧸ Ideal.span {ϖ ^ n})
    (hdc : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ n)))).comp (d (n + 1)) = d n)
    (hdf : ∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap R A ϖ ^ n}) (algebraMap R A)
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d n) = c n)
    (τC : 𝒪 →+* C) (τR : 𝒪 →+* R)
    (hτ : ∀ n : ℕ, (c n).comp τC = (Ideal.Quotient.mk _).comp ((algebraMap R A).comp τR)) :
    ∀ (n : ℕ) (o : 𝒪), d n (τC o) = Ideal.Quotient.mk (Ideal.span {ϖ ^ n}) (τR o) := by
  let c' : ∀ n : ℕ, 𝒪 →+* A ⧸ Ideal.span {algebraMap R A ϖ ^ n} := fun n => (c n).comp τC
  have hc' : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap R A ϖ) (Nat.le_succ n)))).comp (c' (n + 1)) = c' n :=
    fun n => by show (_ : _ →+* _).comp ((c (n + 1)).comp τC) = (c n).comp τC; rw [← RingHom.comp_assoc, hc n]
  have hG' : ∀ (n : ℕ) (g : G) (o : 𝒪) (a : A), Ideal.Quotient.mk _ a = c' n o →
      Ideal.Quotient.mk (Ideal.span {algebraMap R A ϖ ^ n}) (g • a) = c' n o := fun n g o a ha => hG n g (τC o) a ha
  obtain ⟨d', -, huniq'⟩ :=
    ringHom_existsUnique_aux R A 𝒪 G hinj hinv ϖ c' hc' hG'
  have h1 : (fun n => (d n).comp τC) = d' := by
    apply huniq'
    refine ⟨fun n => ?_, fun n => ?_⟩
    · show (_ : _ →+* _).comp ((d (n + 1)).comp τC) = (d n).comp τC
      rw [← RingHom.comp_assoc, hdc n]
    · show (_ : _ →+* _).comp ((d n).comp τC) = (c n).comp τC
      rw [← RingHom.comp_assoc, hdf n]
  have h2 : (fun n => (Ideal.Quotient.mk (Ideal.span {ϖ ^ n})).comp τR) = d' := by
    apply huniq'
    refine ⟨fun n => ?_, fun n => ?_⟩
    · rfl
    · show _ = c' n
      rw [show c' n = (c n).comp τC from rfl, hτ]
      apply RingHom.ext
      intro o
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.quotientMap_mk]
      rfl
  intro n o
  have := congrFun (h1.trans h2.symm) n
  exact congrArg (fun φ : 𝒪 →+* _ => φ o) this

end Compat

end SchemeNilpFactor

end FormalInvFactor29

open FormalInvFactor29 FormalInvFactor29.SchemeNilpFactor

/-- **Nilpotent points factor through a finite quotient.** Let a finite group `G` act on `M` over
`Spec 𝒪`, with `𝒪` Noetherian, and let `p : M ⟶ X` be a `G`-invariant morphism over `Spec 𝒪` that
is integral and affine, with `X` affine, `M` and `X` locally of finite type over `𝒪`, `p` injective
on global sections, and the global sections of `X` mapping onto the `G`-invariant global sections
of `M`. Fix `π : 𝒪` and an affine `T` over `Spec 𝒪`. Then every `G`-invariant family `u` of maps
from the points of `M` to the points of `T`, defined on the `𝒪`-algebras in which `π` is nilpotent
and natural in them, factors through `p` as such a family `ubar` on the points of `X`, and `ubar`
is the only one that does. -/
theorem AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (π : 𝒪)
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪))
    (hlft : LocallyOfFiniteType fM) (hlftX : LocallyOfFiniteType f)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M) (hover : ∀ g : G, (ρ g).asIso.hom ≫ fM = fM)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).asIso.hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsec : Function.Injective p.appTop.hom)
    (hinv : Set.range p.appTop.hom = {s | ∀ g : G, (ρ g).asIso.hom.appTop.hom s = s})
    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (u : ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) →
      (Scheme.pointsOver fM).obj B → (Scheme.pointsOver t).obj B)
    (hu_nat : ∀ (B B' : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B') (x : (Scheme.pointsOver fM).obj B),
      u B' hB' ((Scheme.pointsOver fM).map φ x) = (Scheme.pointsOver t).map φ (u B hB x))
    (hu_inv : ∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : G)
      (y : (Scheme.pointsOver fM).obj B),
      u B hB ((Scheme.pointsOver.mapHom fM fM (ρ g).asIso.hom (hover g)).app B y) = u B hB y)
    (hX : IsAffine X) (hT : IsAffine T) :
    ∃ ubar : ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) →
        (Scheme.pointsOver f).obj B → (Scheme.pointsOver t).obj B,
      (∀ (B B' : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B') (x : (Scheme.pointsOver f).obj B),
        ubar B' hB' ((Scheme.pointsOver f).map φ x) =
          (Scheme.pointsOver t).map φ (ubar B hB x)) ∧
      (∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
        (y : (Scheme.pointsOver fM).obj B),
        ubar B hB ((Scheme.pointsOver.mapHom fM f p hp).app B y) = u B hB y) ∧
      ∀ u' : ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.pointsOver f).obj B → (Scheme.pointsOver t).obj B,
        (∀ (B B' : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B ⟶ B') (x : (Scheme.pointsOver f).obj B),
          u' B' hB' ((Scheme.pointsOver f).map φ x) =
            (Scheme.pointsOver t).map φ (u' B hB x)) →
        (∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (y : (Scheme.pointsOver fM).obj B),
          u' B hB ((Scheme.pointsOver.mapHom fM f p hp).app B y) = u B hB y) →
        ∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
          (z : (Scheme.pointsOver f).obj B), u' B hB z = ubar B hB z := by
  classical
  haveI : IsAffine X := hX
  haveI : IsAffine T := hT
  haveI : IsAffineHom p := haff
  haveI : IsAffine M := isAffine_of_isAffineHom p
  haveI : Fintype G := Fintype.ofFinite G

  letI algA : Algebra 𝒪 Γ(M, ⊤) := (baseHom fM).toAlgebra
  letI algR : Algebra 𝒪 Γ(X, ⊤) := (baseHom f).toAlgebra
  letI algRA : Algebra Γ(X, ⊤) Γ(M, ⊤) := p.appTop.hom.toAlgebra
  letI act : MulSemiringAction G Γ(M, ⊤) := sectionsAction ρ
  have hι : ∀ r : Γ(X, ⊤), algebraMap Γ(X, ⊤) Γ(M, ⊤) r = p.appTop.hom r := fun _ => rfl
  have hbase : ∀ o : 𝒪, baseHom fM o = p.appTop.hom (baseHom f o) := by
    intro o
    show (fM.appTop.hom.comp _) o = p.appTop.hom ((f.appTop.hom.comp _) o)
    rw [← hp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rfl
  haveI : IsScalarTower 𝒪 Γ(X, ⊤) Γ(M, ⊤) := IsScalarTower.of_algebraMap_eq hbase
  have hρapp : ∀ (g : G) (r : Γ(X, ⊤)), (ρ g).asIso.hom.appTop.hom (p.appTop.hom r) = p.appTop.hom r := by
    intro g r
    have := congrArg (fun q : M ⟶ X => q.appTop.hom r) (hρp g)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hcomm : ∀ (g : G) (o : 𝒪), (ρ g).asIso.hom.appTop.hom (baseHom fM o) = baseHom fM o := fun g o => by
    rw [hbase, hρapp]
  haveI : SMulCommClass G Γ(X, ⊤) Γ(M, ⊤) := ⟨fun g r a => by
    rw [Algebra.smul_def, Algebra.smul_def, sectionsAction_smul, sectionsAction_smul, map_mul, hι, hρapp]⟩

  have hftR : (baseHom f).FiniteType := by
    have h1 : f.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hlftX
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).symm.commRingCatIsoToRingEquiv.surjective)
  haveI : IsNoetherianRing Γ(X, ⊤) := @Algebra.FiniteType.isNoetherianRing 𝒪 Γ(X, ⊤) _ _ algR hftR _
  have hftA : (baseHom fM).FiniteType := by
    have h1 : fM.appTop.hom.FiniteType := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp hlft
    exact h1.comp (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of 𝒪)).symm.commRingCatIsoToRingEquiv.surjective)
  haveI : Algebra.FiniteType 𝒪 Γ(M, ⊤) := hftA
  haveI : Algebra.FiniteType Γ(X, ⊤) Γ(M, ⊤) := Algebra.FiniteType.of_restrictScalars_finiteType 𝒪 _ _
  have hintp : p.appTop.hom.IsIntegral := hint.isIntegral_app ⊤ (isAffineOpen_top X)
  haveI : Algebra.IsIntegral Γ(X, ⊤) Γ(M, ⊤) := ⟨fun a => hintp a⟩
  haveI : Module.Finite Γ(X, ⊤) Γ(M, ⊤) := Algebra.IsIntegral.finite
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) Γ(M, ⊤)) := hsec
  have hinvA : ∀ a : Γ(M, ⊤), (∀ g : G, g • a = a) → a ∈ Set.range (algebraMap Γ(X, ⊤) Γ(M, ⊤)) := by
    intro a ha
    have : a ∈ Set.range p.appTop.hom := by
      rw [hinv]
      intro g
      have h1 := ha g⁻¹
      rw [sectionsAction_smul, inv_inv] at h1
      exact h1
    exact this

  let πR : Γ(X, ⊤) := baseHom f π
  let πA : Γ(M, ⊤) := algebraMap Γ(X, ⊤) Γ(M, ⊤) πR
  have hπA : algebraMap 𝒪 Γ(M, ⊤) π = πA := hbase π
  have hBn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(M, ⊤) ⧸ Ideal.span {πA ^ n}) π) := fun n => ⟨n, by
    show Ideal.Quotient.mk (Ideal.span {πA ^ n}) (algebraMap 𝒪 Γ(M, ⊤) π) ^ n = 0
    rw [hπA, show Ideal.Quotient.mk (Ideal.span {πA ^ n}) πA ^ n = Ideal.Quotient.mk (Ideal.span {πA ^ n}) (πA ^ n) from
      (map_pow _ _ _).symm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl⟩
  have hRn : ∀ n : ℕ, IsNilpotent (algebraMap 𝒪 (Γ(X, ⊤) ⧸ Ideal.span {πR ^ n}) π) := fun n => ⟨n, by
    show Ideal.Quotient.mk (Ideal.span {πR ^ n}) πR ^ n = 0
    rw [show Ideal.Quotient.mk (Ideal.span {πR ^ n}) πR ^ n = Ideal.Quotient.mk (Ideal.span {πR ^ n}) (πR ^ n) from
      (map_pow _ _ _).symm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl⟩
  let zT : ∀ n : ℕ, (Scheme.pointsOver t).obj (.of 𝒪 (Γ(M, ⊤) ⧸ Ideal.span {πA ^ n})) :=
    fun n => u _ (hBn n) (canPt fM πA n)
  let c : ∀ n : ℕ, Γ(T, ⊤) →+* Γ(M, ⊤) ⧸ Ideal.span {πA ^ n} := fun n => toHom (zT n).1
  have hc : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow πA (Nat.le_succ n)))).comp (c (n + 1)) = c n :=
    tower_compat fM t π u hu_nat πA hBn
  have hπAinv : ∀ g : G, (ρ g).asIso.hom.appTop.hom πA = πA := fun g => hρapp g πR
  have hG : ∀ (n : ℕ) (g : G) (zC : Γ(T, ⊤)) (a : Γ(M, ⊤)), Ideal.Quotient.mk _ a = c n zC →
      Ideal.Quotient.mk (Ideal.span {πA ^ n}) (g • a) = c n zC := by
    intro n g zC a ha
    rw [sectionsAction_smul]
    exact tower_invariant fM t π ρ hover u hu_nat hu_inv πA hπAinv hcomm hBn n g⁻¹ zC a ha

  obtain ⟨d, ⟨hdc, hdf⟩, huniq⟩ :=
    ringHom_existsUnique_aux Γ(X, ⊤) Γ(M, ⊤) Γ(T, ⊤) G
      hinj hinvA πR c hc hG

  have hdO : ∀ (n : ℕ) (o : 𝒪), d n (baseHom t o) = Ideal.Quotient.mk (Ideal.span {πR ^ n}) (baseHom f o) :=
    descent_comp_eq G hinj hinvA πR c hc hG d hdc hdf (baseHom t) (baseHom f) (fun n => by
      show (toHom (zT n).1).comp (baseHom t) = _
      rw [toHom_comp_baseHom t (zT n).1 (zT n).2]
      exact RingHom.ext fun o => by show Ideal.Quotient.mk _ (baseHom fM o) = _; rw [hbase]; rfl)

  have hηover : ∀ (B : CommAlgCat.{0} 𝒪) (x : (Scheme.pointsOver f).obj B),
      (toHom x.1).comp (baseHom f) = algebraMap 𝒪 B := fun B x => toHom_comp_baseHom f x.1 x.2
  have hxkill : ∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x : (Scheme.pointsOver f).obj B), ∀ a ∈ Ideal.span {πR ^ hB.choose}, toHom x.1 a = 0 :=
    fun B hB x => kill_of_pow_eq_zero f π (toHom x.1) (hηover B x) hB.choose hB.choose_spec
  let ubar : ∀ B : CommAlgCat.{0} 𝒪, IsNilpotent (algebraMap 𝒪 B π) →
      (Scheme.pointsOver f).obj B → (Scheme.pointsOver t).obj B := fun B hB x =>
    ⟨ofHom (evHom d (toHom x.1) hB.choose (hxkill B hB x)),
      ofHom_over t _ (evHom_comp_baseHom f t d hdO (toHom x.1) (hηover B x) _ _)⟩
  have hubar : ∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x : (Scheme.pointsOver f).obj B),
      (ubar B hB x).1 = ofHom (evHom d (toHom x.1) hB.choose (hxkill B hB x)) :=
    fun _ _ _ => rfl

  have hubar_any : ∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x : (Scheme.pointsOver f).obj B) (N : ℕ) (hN : ∀ a ∈ Ideal.span {πR ^ N}, toHom x.1 a = 0),
      (ubar B hB x).1 = ofHom (evHom d (toHom x.1) N hN) := fun B hB x N hN => by
    rw [hubar, evHom_indep d hdc (toHom x.1) hB.choose N (hxkill B hB x) hN]

  have hnat : ∀ (B B' : CommAlgCat.{0} 𝒪)
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B ⟶ B') (x : (Scheme.pointsOver f).obj B),
      ubar B' hB' ((Scheme.pointsOver f).map φ x) = (Scheme.pointsOver t).map φ (ubar B hB x) := by
    intro B B' hB hB' φ x
    have hx' : toHom ((Scheme.pointsOver f).map φ x).1 = φ.hom.toRingHom.comp (toHom x.1) :=
      toHom_specMap_comp φ.hom.toRingHom x.1
    have hkφ : ∀ a ∈ Ideal.span {πR ^ hB.choose}, φ.hom.toRingHom.comp (toHom x.1) a = 0 :=
      fun a ha => by rw [RingHom.comp_apply, hxkill B hB x a ha, map_zero]
    have hkφ' : ∀ a ∈ Ideal.span {πR ^ hB.choose},
        toHom ((Scheme.pointsOver f).map φ x).1 a = 0 := by
      rw [hx']; exact hkφ
    apply Subtype.ext
    rw [hubar_any B' hB' _ hB.choose hkφ']
    show ofHom _ = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ ofHom _
    rw [specMap_comp_ofHom, comp_evHom d φ.hom.toRingHom (toHom x.1) hB.choose (hxkill B hB x) hkφ]
    congr 1
    exact evHom_congr d hx' _ _ _

  have hpbase : p.appTop.hom.comp (baseHom f) = baseHom fM := RingHom.ext fun o => (hbase o).symm
  have hfac : ∀ (B : CommAlgCat.{0} 𝒪) (hB : IsNilpotent (algebraMap 𝒪 B π))
      (y : (Scheme.pointsOver fM).obj B),
      ubar B hB ((Scheme.pointsOver.mapHom fM f p hp).app B y) = u B hB y := by
    intro B hB y
    have hN : algebraMap 𝒪 B π ^ hB.choose = 0 := hB.choose_spec
    have hξ : (toHom y.1).comp (baseHom fM) = algebraMap 𝒪 B := toHom_comp_baseHom fM y.1 y.2
    have hξkill : ∀ a ∈ Ideal.span {πA ^ hB.choose}, toHom y.1 a = 0 := by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, map_pow, ← hπA, show toHom y.1 (algebraMap 𝒪 Γ(M, ⊤) π) = algebraMap 𝒪 B π from by rw [← hξ]; rfl,
        hN, mul_zero]
    obtain ⟨ξN, hξN, hy⟩ := eq_map_canPt fM πA y hB.choose hξkill
    have hη : toHom ((Scheme.pointsOver.mapHom fM f p hp).app B y).1 =
        (toHom y.1).comp p.appTop.hom :=
      toHom_comp y.1 p
    have hk1 : ∀ a ∈ Ideal.span {πR ^ hB.choose}, (toHom y.1).comp (algebraMap Γ(X, ⊤) Γ(M, ⊤)) a = 0 :=
      kill_of_pow_eq_zero f π _ (by show ((toHom y.1).comp p.appTop.hom).comp (baseHom f) = _; rw [RingHom.comp_assoc, hpbase, hξ]) _ hN
    have hkη : ∀ a ∈ Ideal.span {πR ^ hB.choose},
        toHom ((Scheme.pointsOver.mapHom fM f p hp).app B y).1 a = 0 := by
      rw [hη]; exact hk1
    apply Subtype.ext
    rw [hubar_any B hB ((Scheme.pointsOver.mapHom fM f p hp).app B y) hB.choose hkη]
    conv_rhs => rw [hy, hu_nat _ _ (hBn hB.choose) hB ξN (canPt fM πA hB.choose)]
    show ofHom _ = Spec.map (CommRingCat.ofHom ξN.hom.toRingHom) ≫ (zT hB.choose).1
    conv_rhs => rw [← ofHom_toHom (zT hB.choose).1, specMap_comp_ofHom]
    congr 1
    have step1 : evHom d (toHom ((Scheme.pointsOver.mapHom fM f p hp).app B y).1) hB.choose hkη =
        evHom d ((toHom y.1).comp (algebraMap Γ(X, ⊤) Γ(M, ⊤))) hB.choose hk1 := by congr 1
    rw [step1, evHom, ← lift_comp_quotientMap (X := X) (algebraMap Γ(X, ⊤) Γ(M, ⊤)) (toHom y.1) hB.choose hξkill hk1,
      RingHom.comp_assoc, hdf hB.choose]
    show _ = ξN.hom.toRingHom.comp (c hB.choose)
    congr 1
    exact Ideal.Quotient.ringHom_ext (hξN.symm ▸ rfl)
  refine ⟨ubar, hnat, hfac, ?_⟩

  intro u' hu'nat hu'fac B hB x

  obtain ⟨ηN, hηN, hx⟩ := eq_map_canPt f πR x hB.choose (hxkill B hB x)
  rw [hx, hu'nat _ _ (hRn hB.choose) hB ηN, hnat _ _ (hRn hB.choose) hB ηN]
  congr 1

  let d' : ∀ n : ℕ, Γ(T, ⊤) →+* Γ(X, ⊤) ⧸ Ideal.span {πR ^ n} := fun n => toHom (u' _ (hRn n) (canPt f πR n)).1
  have hd'c : ∀ n : ℕ, (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow πR (Nat.le_succ n)))).comp (d' (n + 1)) = d' n :=
    tower_compat f t π u' hu'nat πR hRn
  have hd'f : ∀ n : ℕ, (Ideal.quotientMap (Ideal.span {algebraMap Γ(X, ⊤) Γ(M, ⊤) πR ^ n}) (algebraMap Γ(X, ⊤) Γ(M, ⊤))
      (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, ← map_pow]; exact Ideal.subset_span rfl)).comp (d' n) = c n := by
    intro n

    let ιn : (Γ(X, ⊤) ⧸ Ideal.span {πR ^ n}) →ₐ[𝒪] (Γ(M, ⊤) ⧸ Ideal.span {πA ^ n}) :=
      Ideal.quotientMapₐ _ (AlgHom.mk (algebraMap Γ(X, ⊤) Γ(M, ⊤)) (fun o => (hbase o).symm))
        (by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact Ideal.subset_span (by rw [map_pow]; rfl))
    have hpt : (Scheme.pointsOver f).map (CommAlgCat.ofHom ιn) (canPt f πR n) =
        (Scheme.pointsOver.mapHom fM f p hp).app _ (canPt fM πA n) := by
      apply Subtype.ext
      show Spec.map (CommRingCat.ofHom ιn.toRingHom) ≫ ofHom (Ideal.Quotient.mk _) = ofHom (Ideal.Quotient.mk _) ≫ p
      rw [specMap_comp_ofHom, ← ofHom_toHom (ofHom (Ideal.Quotient.mk (Ideal.span {πA ^ n})) ≫ p), toHom_comp, toHom_ofHom]
      congr 1
    have h1 := hu'nat _ _ (hRn n) (hBn n) (CommAlgCat.ofHom ιn) (canPt f πR n)
    rw [hpt, hu'fac _ (hBn n)] at h1

    show _ = toHom (zT n).1
    show _ = toHom (u _ (hBn n) (canPt fM πA n)).1
    rw [h1]
    have := toHom_specMap_comp ιn.toRingHom (u' _ (hRn n) (canPt f πR n)).1
    refine (Eq.trans ?_ this.symm)
    rfl
  have hdd : d' = d := huniq d' ⟨hd'c, hd'f⟩

  apply Subtype.ext
  have hkn : ∀ a ∈ Ideal.span {πR ^ hB.choose}, toHom (canPt f πR hB.choose).1 a = 0 := by
    intro a ha
    rw [canPt_val, toHom_ofHom]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [hubar_any _ (hRn hB.choose) _ hB.choose hkn, ← ofHom_toHom (u' _ (hRn hB.choose) (canPt f πR hB.choose)).1]
  congr 1
  show d' hB.choose = _
  rw [hdd, evHom]
  conv_lhs => rw [← RingHom.id_comp (d hB.choose)]
  congr 1
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro r
  rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.lift_mk, RingHom.id_apply, canPt_val, toHom_ofHom]
