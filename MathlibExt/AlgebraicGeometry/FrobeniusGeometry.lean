/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Frobenius.lean, under Apache 2.0.
The source has no individual copyright or author header.
Modifications: remove registry attributes/dependencies, move the namespace,
and add the prime-field specialization used by geometric F/V maps.

The naturality proof is adapted from TauCeti, revision
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/AlgebraicGeometry/Frobenius/Basic.lean.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors. Released under Apache 2.0.
Modification: use the ported absolute-Frobenius and restriction APIs.
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Actual absolute and geometric scheme Frobenius

The endomorphism fixes scheme points and raises actual regular functions
on every open to the prime power. Vanishing of p on global functions is
restricted to each open, including the zero-ring case. Over a finite field,
the appropriate iterate is an actual morphism in the scheme slice.

These constructions and normalizations are complete source ports. They do
not supply an arbitrary Frobenius on a named cohomology group.

References: Stacks Project, Tags 03SM and 03SQ.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace MathlibExt.AlgebraicGeometry.FrobeniusGeometry

/-- A scheme is **in characteristic `p`** when `p` vanishes in its ring of global sections. -/
abbrev IsInCharacteristic (X : Scheme.{u}) (p : ℕ) : Prop :=
  (p : Γ(X, ⊤)) = 0

/-- On a scheme in characteristic `p` the integer `p` vanishes in the sections over every
open, by restricting the vanishing on global sections. -/
lemma cast_eq_zero_of_isInCharacteristic {X : Scheme.{u}} {p : ℕ}
    (hX : IsInCharacteristic X p) (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (X.presheaf.map (homOfLE (show U ≤ (⊤ : X.Opens) from le_top)).op) hX

/-- In a commutative ring in which a prime `p` vanishes, taking `p`-th powers is a ring
endomorphism. The zero ring, where `p` need not be the characteristic, is covered as well: the
`p`-th power map is the identity there. -/
noncomputable def primePowerEndomorphism (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) : R →+* R := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    letI : CharP R p := by
      rw [← ringChar.eq_iff]
      exact ((Nat.dvd_prime Fact.out).mp (ringChar.dvd hp)).resolve_left
        CharP.ringChar_ne_one
    exact frobenius R p
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact RingHom.id R

/-- The prime power endomorphism is given pointwise by taking `p`-th powers. -/
@[simp]
lemma primePowerEndomorphism_apply (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) = 0) (x : R) : primePowerEndomorphism R p hp x = x ^ p := by
  classical
  rw [primePowerEndomorphism]
  split
  · rfl
  · rename_i hR
    let _ : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

/-- **Stacks Project, Tag 03SM.** The absolute Frobenius of a scheme in characteristic `p`: it
is the identity on points and the `p`-th power map on the structure sheaf. -/
noncomputable def absoluteFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) : X ⟶ X := by
  let α : X.presheaf ⟶ X.presheaf :=
    { app := fun U ↦ CommRingCat.ofHom <|
        primePowerEndomorphism _ p (cast_eq_zero_of_isInCharacteristic hX U.unop)
      naturality := by
        intro U V f
        ext g
        change primePowerEndomorphism _ p
            (cast_eq_zero_of_isInCharacteristic hX V.unop) ((X.presheaf.map f) g) =
          X.presheaf.map f (primePowerEndomorphism _ p
            (cast_eq_zero_of_isInCharacteristic hX U.unop) g)
        rw [primePowerEndomorphism_apply, primePowerEndomorphism_apply, map_pow] }
  let f : X.toPresheafedSpace ⟶ X.toPresheafedSpace := { base := 𝟙 _, c := α }
  refine Scheme.Hom.mk <| LocallyRingedSpace.homMk (InducedCategory.homMk f) ?_
  rw [InducedCategory.homMk_hom]
  dsimp only [f]
  intro x
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨U, hxU, g, rfl⟩ := X.presheaf.exists_germ_eq a
  change IsUnit (X.presheaf.germ U x hxU g)
  apply (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  change IsUnit (X.presheaf.germ U x hxU
    (primePowerEndomorphism _ p (cast_eq_zero_of_isInCharacteristic hX U) g)) at ha
  simpa only [primePowerEndomorphism_apply, map_pow] using ha

/-- The absolute Frobenius is the identity on the underlying topological space. -/
@[simp]
lemma absoluteFrobenius_base (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) :
    (absoluteFrobenius X p hX).base = 𝟙 (X : TopCat) := rfl

/-- The absolute Frobenius fixes every point. -/
@[simp]
lemma absoluteFrobenius_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (x : X) : absoluteFrobenius X p hX x = x := rfl

/-- Every open set is its own inverse image under the absolute Frobenius. -/
lemma absoluteFrobenius_preimage (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : X.Opens) :
    (absoluteFrobenius X p hX) ⁻¹ᵁ U = U := rfl

/-- On every open set, the map induced by the absolute Frobenius raises sections to their
`p`-th powers. -/
lemma absoluteFrobenius_app_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : X.Opens) (g : Γ(X, U)) :
    (absoluteFrobenius X p hX).app U g = g ^ p :=
  primePowerEndomorphism_apply _ p (cast_eq_zero_of_isInCharacteristic hX U) g

/-- Identifying an open with its inverse image, the map on sections induced by the absolute
Frobenius is the `p`-th power map. -/
@[simp]
lemma absoluteFrobenius_appLE_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (U : X.Opens)
    (e : U ≤ (absoluteFrobenius X p hX) ⁻¹ᵁ U) (g : Γ(X, U)) :
    (absoluteFrobenius X p hX).appLE U U e g = g ^ p := by
  change X.presheaf.map (𝟙 (op U)) ((absoluteFrobenius X p hX).app U g) = g ^ p
  rw [X.presheaf.map_id, absoluteFrobenius_app_apply]
  simp

/-- An endomorphism which fixes points and raises sections to their `p`-th powers is the
absolute Frobenius. -/
lemma eq_absoluteFrobenius (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (f : X ⟶ X) (hf : f.base = 𝟙 (X : TopCat))
    (hf' : ∀ (U : X.Opens) (g : Γ(X, U)), f.appLE U U (by simp [hf]) g = g ^ p) :
    f = absoluteFrobenius X p hX := by
  apply Scheme.Hom.ext (hf.trans (absoluteFrobenius_base X p hX).symm)
  intro U
  ext g
  change f.appLE U U (by simp [hf]) g = (absoluteFrobenius X p hX).app U g
  rw [hf', absoluteFrobenius_app_apply]

/-- On global sections, the map induced by the `n`-fold absolute Frobenius raises sections to
their `p ^ n`-th powers. -/
@[simp]
lemma absoluteFrobenius_pow_appTop_apply (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (n : ℕ) (g : Γ(X, ⊤)) :
    (End.asHom (End.of (absoluteFrobenius X p hX) ^ n)).appTop g = g ^ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, End.mul_asHom, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih,
      show (absoluteFrobenius X p hX).appTop (g ^ p ^ n) = (g ^ p ^ n) ^ p from
        absoluteFrobenius_app_apply X p hX ⊤ _, ← pow_mul, ← pow_succ]

/-- A scheme over a ring in which `p` vanishes is in characteristic `p`. -/
lemma isInCharacteristic_of_over {R : Type u} [CommRing R] {p : ℕ} [CharP R p]
    (X : Over (Spec (.of R))) : IsInCharacteristic X.left p := by
  let φ : R →+* Γ(X.left, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop).hom
  change (p : Γ(X.left, ⊤)) = 0
  rw [← map_natCast φ, CharP.cast_eq_zero R p]
  exact map_zero φ

/-- On a scheme over a finite field with `p ^ f` elements, the `f`-fold absolute Frobenius is a
morphism over the field: on global sections it raises to the `p ^ f`-th power, which fixes the
image of the field because `a ^ p ^ f = a` there. -/
lemma absoluteFrobenius_pow_comp_hom {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) :
    End.asHom (End.of (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f) ≫
      X.hom = X.hom := by
  have key (a : k) : ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom a ^ p ^ f =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom a := by
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  refine ext_to_Spec ?_
  change ((Scheme.ΓSpecIso (.of k)).inv ≫
      (End.asHom (End.of (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f) ≫
        X.hom).appTop : CommRingCat.of k ⟶ Γ(X.left, ⊤)) =
    (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  ext a
  rw [CommRingCat.comp_apply, absoluteFrobenius_pow_appTop_apply]
  exact key a

/-- **Stacks Project, Tag 03SQ.** The geometric Frobenius of a scheme over a finite field of
characteristic `p` and cardinality `p ^ f`. It is the `f`-fold absolute Frobenius, bundled with
its canonical structure as a morphism over the field. -/
noncomputable def geometricFrobenius {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) : X ⟶ X :=
  Over.homMk
    (End.asHom (End.of
      (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f))
    (absoluteFrobenius_pow_comp_hom X p f hcard)

/-- The underlying scheme morphism of the geometric Frobenius is the `f`-fold absolute
Frobenius. -/
@[simp]
lemma geometricFrobenius_left {k : Type u} [Field k] [Fintype k]
    (X : Over (Spec (.of k))) (p f : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ f) :
    (geometricFrobenius X p f hcard).left =
      End.asHom (End.of
        (absoluteFrobenius X.left p (isInCharacteristic_of_over X)) ^ f) := rfl


/-- Frobenius on a restricted section is the prime power of its restriction. -/
theorem absoluteFrobenius_appLE_restrict (X : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (U V : X.Opens)
    (e : V ≤ absoluteFrobenius X p hX ⁻¹ᵁ U) (s : Γ(X, U)) :
    (absoluteFrobenius X p hX).appLE U V e s =
      X.presheaf.map (homOfLE e).op s ^ p := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply,
    absoluteFrobenius_app_apply]
  exact map_pow (X.presheaf.map (homOfLE e).op).hom s p

/-- Every actual scheme morphism in characteristic p commutes with Frobenius. -/
theorem absoluteFrobenius_naturality {X Y : Scheme.{u}} (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (f : X ⟶ Y) :
    absoluteFrobenius X p hX ≫ f = f ≫ absoluteFrobenius Y p hY := by
  refine Scheme.Hom.ext (by simp) fun U => ?_
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.comp_appLE,
    Scheme.Hom.comp_appLE,
    Scheme.Hom.app_eq_appLE (f := absoluteFrobenius Y p hY)]
  ext s
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply,
    absoluteFrobenius_appLE_restrict, map_pow]
  refine (absoluteFrobenius_appLE_restrict X p hX _ _ _ _).trans
    (congrArg (· ^ p) ?_)
  exact congr(($(f.map_appLE _ _)).hom s).symm

/-- Frobenius over the actual prime field, as a scheme morphism over F_p. -/
def primeFieldFrobenius (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of (ZMod p)))) : X ⟶ X :=
  geometricFrobenius X p 1 (by simp)

/-- Prime-field Frobenius is the actual absolute Frobenius. -/
theorem primeFieldFrobenius_left (p : ℕ) [Fact p.Prime]
    (X : Over (Spec (CommRingCat.of (ZMod p)))) :
    (primeFieldFrobenius p X).left =
      absoluteFrobenius X.left p (isInCharacteristic_of_over X) := by
  simp [primeFieldFrobenius]

/-- Prime-field scheme Frobenius is natural on the actual slice category. -/
theorem primeFieldFrobenius_naturality (p : ℕ) [Fact p.Prime]
    {X Y : Over (Spec (CommRingCat.of (ZMod p)))} (f : X ⟶ Y) :
    primeFieldFrobenius p X ≫ f = f ≫ primeFieldFrobenius p Y := by
  apply Over.OverMorphism.ext
  simpa only [Over.comp_left, primeFieldFrobenius_left] using
    absoluteFrobenius_naturality p (isInCharacteristic_of_over X)
      (isInCharacteristic_of_over Y) f.left

end MathlibExt.AlgebraicGeometry.FrobeniusGeometry
