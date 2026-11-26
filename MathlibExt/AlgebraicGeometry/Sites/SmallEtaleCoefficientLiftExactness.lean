/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleLocalShortExact
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGeometricStalkExactness

/-!
# Exactness after lifting small étale coefficients

Let X be a scheme in universe u and F′ → F → F″ abelian sheaves on its
small étale site with coefficients in an independent universe w.
Assume the first map is injective on sections over each étale object,
its image is the kernel of the second map on those sections, and the
second map is locally surjective on covering étale sieves.

Lifting all coefficient groups to c = max(u, w) preserves these conditions
with the same covering sieves. The lifted arrows form a categorical short
exact sequence of AddCommGrpCat c-valued sheaves. A morphism between two
such sequences is lifted by applying the coefficient-lift functor to its
three component maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections

variable {X : Scheme.{u}}
  {F' F F'' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
  {a : F' ⟶ F} {b : F ⟶ F''}

/-- Let X be a scheme in universe u, F′, F, F″ abelian sheaves
on its small étale site with coefficients in universe w, and
a : F′ → F, b : F → F″ sheaf morphisms. Assume every a_U is injective,
range(a_U) = ker(b_U) on every étale object U, and b is locally
surjective on covering étale sieves. Put c = max(u, w).
The coefficient lift L from w to c preserves these sectionwise and
local conditions: L(a)_U is injective, range(L(a)_U) = ker(L(b)_U),
and L(b) is locally surjective using the same covering sieves. -/
theorem coefficientLift_localShortExact (h : originalSmallEtaleLocalShortExact a b) :
    originalSmallEtaleLocalShortExact
      ((liftCoefficients.{u, w} X).map a) ((liftCoefficients.{u, w} X).map b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro U x y hxy
    apply ULift.ext
    apply h.1 U
    exact congrArg ULift.down hxy
  · intro U
    ext x
    cases x with
    | up x =>
      constructor
      · rintro ⟨y, hy⟩
        have hra : x ∈ Set.range (a.hom.app (op U)) :=
          ⟨y.down, congrArg ULift.down hy⟩
        rw [h.2.1 U] at hra
        change ULift.up (b.hom.app (op U) x) = ULift.up (0 : F''.obj.obj (op U))
        exact congrArg ULift.up hra
      · intro hx
        have hbx : b.hom.app (op U) x = 0 := congrArg ULift.down hx
        have hra : x ∈ Set.range (a.hom.app (op U)) := by
          rw [h.2.1 U]
          exact hbx
        obtain ⟨y, hy⟩ := hra
        exact ⟨ULift.up y, congrArg ULift.up hy⟩
  · intro U c
    cases c with
    | up c =>
      obtain ⟨R, hR, hlift⟩ := h.2.2 U c
      refine ⟨R, hR, ?_⟩
      intro V p hp
      obtain ⟨d, hd⟩ := hlift V p hp
      exact ⟨ULift.up d, congrArg ULift.up hd⟩

/-- Let X be a scheme in universe u, F′, F, F″ abelian sheaves
on its small étale site with coefficients in universe w, and
a : F′ → F, b : F → F″ sheaf morphisms. Assume every a_U is injective,
range(a_U) = ker(b_U) on every étale object U, and b is locally
surjective on covering étale sieves. Put c = max(u, w).
The lifted sheaves L(F′), L(F), L(F″) with arrows L(a), L(b)
form this short complex in the common coefficient universe c.
The zero-composite equation follows from the image–kernel equality. -/
def coefficientLiftLocalShortComplex (h : originalSmallEtaleLocalShortExact a b) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  originalSmallEtaleLocalShortComplex (coefficientLift_localShortExact h)

/-- Let X be a scheme in universe u, F′, F, F″ abelian sheaves
on its small étale site with coefficients in universe w, and
a : F′ → F, b : F → F″ sheaf morphisms. Assume every a_U is injective,
range(a_U) = ker(b_U) on every étale object U, and b is locally
surjective on covering étale sieves. Put c = max(u, w).
The short complex L(F′) → L(F) → L(F″) is short exact in the
category of AddCommGrpCat c-valued sheaves on the small étale site of X. -/
theorem coefficientLift_shortExact (h : originalSmallEtaleLocalShortExact a b) :
    (coefficientLiftLocalShortComplex h).ShortExact :=
  (smallEtaleCommon_shortExact_iff_local (coefficientLiftLocalShortComplex h)).mpr
    (coefficientLift_localShortExact h)

/-- Let X be a scheme in universe u, F′, F, F″ abelian sheaves
on its small étale site with coefficients in universe w, and
a : F′ → F, b : F → F″ sheaf morphisms. Assume every a_U is injective,
range(a_U) = ker(b_U) on every étale object U, and b is locally
surjective on covering étale sieves. Put c = max(u, w).
For another sequence with the same sectionwise and local conditions
and a sequence morphism α given by three sheaf maps commuting with a
and b, applying L to α₁, α₂, α₃ gives a morphism of the two
coefficient-lifted short complexes in universe c. -/
def coefficientLiftSequenceMorphism
    (h : originalSmallEtaleLocalShortExact a b)
    {G' G G'' : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}}
    {a' : G' ⟶ G} {b' : G ⟶ G''} (h' : originalSmallEtaleLocalShortExact a' b')
    (α : OriginalSmallEtaleLocalShortExactHom h h') :
    coefficientLiftLocalShortComplex h ⟶ coefficientLiftLocalShortComplex h' where
  τ₁ := (liftCoefficients.{u, w} X).map α.τ₁
  τ₂ := (liftCoefficients.{u, w} X).map α.τ₂
  τ₃ := (liftCoefficients.{u, w} X).map α.τ₃
  comm₁₂ := by
    have h := (liftCoefficients.{u, w} X).congr_map α.comm₁₂
    simpa only [Functor.map_comp, coefficientLiftLocalShortComplex,
      originalSmallEtaleLocalShortComplex] using h
  comm₂₃ := by
    have h := (liftCoefficients.{u, w} X).congr_map α.comm₂₃
    simpa only [Functor.map_comp, coefficientLiftLocalShortComplex,
      originalSmallEtaleLocalShortComplex] using h

end AlgebraicGeometry.Scheme.DerivedSections
