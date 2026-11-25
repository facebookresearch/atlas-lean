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

/-! # Exactness of the canonical coefficient lift on the original étale site

The source sequence is locally short exact in its original independent
coefficient universe. Its same covers and literal lifted component maps give
a categorical short exact sequence in the constructed common universe.
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

/-- The original local condition survives the same coefficient lift and covers. -/
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

/-- The lifted original arrows, with zero composite derived from local exactness. -/
def coefficientLiftLocalShortComplex (h : originalSmallEtaleLocalShortExact a b) :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :=
  originalSmallEtaleLocalShortComplex (coefficientLift_localShortExact h)

/-- The actual canonically lifted sequence is categorically short exact. -/
theorem coefficientLift_shortExact (h : originalSmallEtaleLocalShortExact a b) :
    (coefficientLiftLocalShortComplex h).ShortExact :=
  (smallEtaleCommon_shortExact_iff_local (coefficientLiftLocalShortComplex h)).mpr
    (coefficientLift_localShortExact h)

/-- Every original sequence morphism lifts by its same three coefficient maps. -/
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
