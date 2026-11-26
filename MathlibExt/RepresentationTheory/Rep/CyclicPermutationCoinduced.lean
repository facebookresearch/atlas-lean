/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Rep.CyclicPermutation
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Cyclic permutation coefficients and coinduction

Let k be a commutative ring, G a group and
χ:G→Multiplicative(ZMod ℓ) a surjective character. Put H=ker χ.
The cyclic coefficient Pχ(A) is isomorphic to Coind_H^G(Res_H^G A).

The forward function is p↦(g↦g•p(χ_add(g))).
For a chosen lift s_i of i∈ZMod ℓ, the inverse has value
i↦s_i⁻¹•F(s_i). The diagonal corresponds to the Res⊣Coind unit.
Taking cohomology and Shapiro gives Hⁿ(G,Pχ(A))≅Hⁿ(H,Res_H A)
for all n. The statements allow every ℓ, including ℓ=0.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Representation

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- For a surjective character χ:G→Multiplicative(ZMod ℓ),
this chooses s_i∈G with χ(s_i)=Multiplicative.ofAdd(i)
for each i∈ZMod ℓ. -/
noncomputable def cyclicCharacterLift
    {ell : ℕ}
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (i : ZMod ell) : G :=
  Function.surjInv hsurj (Multiplicative.ofAdd i)

@[simp]
theorem cyclicCharacterLift_spec
    {ell : ℕ}
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (i : ZMod ell) :
    chi (cyclicCharacterLift chi hsurj i) = Multiplicative.ofAdd i :=
  Function.surjInv_eq hsurj _

/-- Let k be a commutative ring and G a group in universe u,
and let A be a k-linear G-representation with coefficient carrier u.
Let χ:G→Multiplicative(ZMod ℓ) be surjective and H=ker χ.
Write Pχ(A)=ZMod ℓ→A with (g•p)(i)=g•p(i+χ_add(g)).
The k-linear equivalence Pχ(A)≅Coind_H^G(Res_H A) sends
p to F(g)=g•p(χ_add(g)).
Its inverse uses a lift s_i and has p(i)=s_i⁻¹•F(s_i). -/
noncomputable def cyclicPermutationCoinducedLinearEquiv
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G) :
    cyclicPermutation ell chi A ≃ₗ[k]
      coind chi.ker.subtype (Rep.res chi.ker.subtype A) where
  toFun p :=
    ⟨fun g => A.ρ g (p (Multiplicative.toAdd (chi g))), by
      intro h g
      change A.ρ ((h : G) * g)
          (p (Multiplicative.toAdd (chi ((h : G) * g)))) =
        A.ρ h (A.ρ g (p (Multiplicative.toAdd (chi g))))
      have hh : chi (h : G) = 1 := h.property
      rw [map_mul chi, hh]
      change A.ρ ((h : G) * g) (p (0 + Multiplicative.toAdd (chi g))) = _
      rw [zero_add, map_mul A.ρ]
      rfl⟩
  invFun F (i : ZMod ell) :=
    let s := cyclicCharacterLift chi hsurj i
    A.ρ s⁻¹ (F.1 s)
  map_add' p q := by
    apply Subtype.ext
    funext g
    simp only [Pi.add_apply, map_add]
    rfl
  map_smul' r p := by
    apply Subtype.ext
    funext g
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rfl
  left_inv p := by
    funext i
    let s := cyclicCharacterLift chi hsurj i
    change A.ρ s⁻¹
      (A.ρ s (p (Multiplicative.toAdd (chi s)))) = p i
    rw [cyclicCharacterLift_spec]
    change A.ρ s⁻¹ (A.ρ s (p i)) = p i
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  right_inv F := by
    apply Subtype.ext
    funext g
    let i := Multiplicative.toAdd (chi g)
    let s := cyclicCharacterLift chi hsurj i
    let h : chi.ker := ⟨g * s⁻¹, by
      change chi (g * s⁻¹) = 1
      rw [map_mul, map_inv, cyclicCharacterLift_spec]
      change chi g * (chi g)⁻¹ = 1
      exact mul_inv_cancel _⟩
    have hgs : (h : G) * s = g := by
      change (g * s⁻¹) * s = g
      simp [mul_assoc]
    have hF := F.2 h s
    change F.1 ((h : G) * s) = A.ρ h (F.1 s) at hF
    change A.ρ g (A.ρ s⁻¹ (F.1 s)) = F.1 g
    rw [← Module.End.mul_apply, ← map_mul]
    change A.ρ (g * s⁻¹) (F.1 s) = F.1 g
    rw [← show (h : G) = g * s⁻¹ from rfl, ← hF, hgs]

/-- Let k be a commutative ring and G a group in universe u,
and let A be a k-linear G-representation with coefficient carrier u.
Let χ:G→Multiplicative(ZMod ℓ) be surjective and H=ker χ.
Write Pχ(A)=ZMod ℓ→A with (g•p)(i)=g•p(i+χ_add(g)).
The forward coinduced function has point value
F_p(g)=g•p(χ_add(g)). -/
@[simp]
theorem cyclicPermutationCoinducedLinearEquiv_apply
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G)
    (p : ZMod ell → A) (g : G) :
    ((cyclicPermutationCoinducedLinearEquiv
      ell chi hsurj A p : coind chi.ker.subtype
      (Rep.res chi.ker.subtype A)) : G → A) g =
      A.ρ g (p (Multiplicative.toAdd (chi g))) :=
  by
    unfold cyclicPermutationCoinducedLinearEquiv
    rfl

/-- Let k be a commutative ring and G a group in universe u,
and let A be a k-linear G-representation with coefficient carrier u.
Let χ:G→Multiplicative(ZMod ℓ) be surjective and H=ker χ.
Write Pχ(A)=ZMod ℓ→A with (g•p)(i)=g•p(i+χ_add(g)).
The explicit linear equivalence is G-equivariant and gives
the representation isomorphism Pχ(A)≅Coind_H^G(Res_H A). -/
noncomputable def cyclicPermutationCoinducedIso
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G) :
    cyclicPermutation ell chi A ≅
      coind chi.ker.subtype (Rep.res chi.ker.subtype A) :=
  Rep.mkIso (Representation.Equiv.mk
    (cyclicPermutationCoinducedLinearEquiv ell chi hsurj A)
    (fun x => by
      apply LinearMap.ext
      intro p
      apply Subtype.ext
      funext g
      dsimp only [cyclicPermutationCoinducedLinearEquiv]
      change A.ρ g
          (A.ρ x (p (Multiplicative.toAdd (chi g) +
            Multiplicative.toAdd (chi x)))) =
        A.ρ (g * x)
          (p (Multiplicative.toAdd (chi (g * x))))
      rw [← Module.End.mul_apply, ← map_mul]
      rw [map_mul chi]
      rfl))

@[simp]
theorem cyclicPermutationCoinducedIso_hom_apply
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G)
    (p : ZMod ell → A) (g : G) :
    (((cyclicPermutationCoinducedIso ell chi hsurj A).hom.hom p :
        coind chi.ker.subtype (Rep.res chi.ker.subtype A)) : G → A) g =
      A.ρ g (p (Multiplicative.toAdd (chi g))) :=
  by
    unfold cyclicPermutationCoinducedIso
      cyclicPermutationCoinducedLinearEquiv
    rfl

/-- Let k be a commutative ring and G a group in universe u,
and let A be a k-linear G-representation with coefficient carrier u.
Let χ:G→Multiplicative(ZMod ℓ) be surjective and H=ker χ.
Write Pχ(A)=ZMod ℓ→A with (g•p)(i)=g•p(i+χ_add(g)).
The constant diagonal A→Pχ(A) followed by the coinduction
isomorphism is the unit A→Coind_H^G(Res_H A) of Res_H⊣Coind_H^G. -/
theorem cyclicPermutationDiagonal_comp_coinducedIso
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G) :
    cyclicPermutationDiagonal ell chi A ≫
        (cyclicPermutationCoinducedIso ell chi hsurj A).hom =
      (resCoindAdjunction k chi.ker.subtype).unit.app A := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext g
  change A.ρ g
      ((cyclicPermutationDiagonal ell chi A).hom a
        (Multiplicative.toAdd (chi g))) = A.ρ g a
  rw [cyclicPermutationDiagonal_apply]

end Rep

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Let k be a commutative ring and G a group in universe u,
and let A be a k-linear G-representation with coefficient carrier u.
Let χ:G→Multiplicative(ZMod ℓ) be surjective and H=ker χ.
Write Pχ(A)=ZMod ℓ→A with (g•p)(i)=g•p(i+χ_add(g)).
The coefficient isomorphism induces
Hⁿ(G,Pχ(A))≅Hⁿ(G,Coind_H^G(Res_H A)) for every n∈ℕ. -/
noncomputable def cyclicPermutationCoinducedCohomologyIso
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology (Rep.cyclicPermutation ell chi A) n ≅
      groupCohomology
        (Rep.coind chi.ker.subtype
          (Rep.res chi.ker.subtype A)) n :=
  groupCohomology.mapIso (MulEquiv.refl G)
    (Rep.cyclicPermutationCoinducedLinearEquiv ell chi hsurj A)
    (fun g => by
      apply LinearMap.ext
      intro p
      exact Rep.hom_comm_apply
        (Rep.cyclicPermutationCoinducedIso ell chi hsurj A).hom g p)
    n

@[simp]
theorem cyclicPermutationCoinducedCohomologyIso_hom
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G) (n : ℕ) :
    (cyclicPermutationCoinducedCohomologyIso
      ell chi hsurj A n).hom =
      groupCohomology.map (MonoidHom.id G)
        (Rep.cyclicPermutationCoinducedIso ell chi hsurj A).hom n :=
  rfl

/-- Let k be a commutative ring and G a group in universe u,
and let A be a k-linear G-representation with coefficient carrier u.
Let χ:G→Multiplicative(ZMod ℓ) be surjective and H=ker χ.
Write Pχ(A)=ZMod ℓ→A with (g•p)(i)=g•p(i+χ_add(g)).
Composing the coefficient comparison with Shapiro gives
Hⁿ(G,Pχ(A))≅Hⁿ(H,Res_H A) in every degree n∈ℕ. -/
noncomputable def cyclicPermutationShapiroIso
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology (Rep.cyclicPermutation ell chi A) n ≅
      groupCohomology (Rep.res chi.ker.subtype A) n :=
  cyclicPermutationCoinducedCohomologyIso ell chi hsurj A n ≪≫
    groupCohomology.coindIso (Rep.res chi.ker.subtype A) n

-- Unfolding the projective-resolution Shapiro comparison is expensive.
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring and G a group in universe u,
and let A be a k-linear G-representation with coefficient carrier u.
Let χ:G→Multiplicative(ZMod ℓ) be surjective and H=ker χ.
Write Pχ(A)=ZMod ℓ→A with (g•p)(i)=g•p(i+χ_add(g)).
The forward Shapiro map is the G-cohomology map of
Pχ(A)→Coind_H^G(Res_H A), followed by the usual coinduced
Shapiro isomorphism to H-cohomology. -/
theorem cyclicPermutationShapiroIso_hom
    (ell : ℕ)
    (chi : G →* Multiplicative (ZMod ell))
    (hsurj : Function.Surjective chi) (A : Rep.{u} k G) (n : ℕ) :
    (cyclicPermutationShapiroIso ell chi hsurj A n).hom =
      groupCohomology.map (MonoidHom.id G)
          (Rep.cyclicPermutationCoinducedIso ell chi hsurj A).hom n ≫
        (groupCohomology.coindIso
          (Rep.res chi.ker.subtype A) n).hom := by
  rfl

end groupCohomology
