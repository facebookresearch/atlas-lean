/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Homotopy
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.Hom
public import MathlibExt.Analysis.CStarAlgebra.Homotopy
public import Mathlib.Data.Quot

/-!
# Fixed-hom functoriality and ordinary homomorphism inclusion

Only the composing map in pre/postcomposition is an actual star hom.
The other family remains arbitrary and nonlinear. No same-time composition
of two arbitrary asymptotic families is defined.

Ordinary classes are the real quotient of the existing point-norm Homotopic
predicate. Its proven equivalence is reused, and ofHom descends through the
actual constructed asymptotic homotopy quotient.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe uA uB uC uD

namespace NonUnitalStarAlgHom

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- The ordinary homotopy setoid, using the existing real hom-valued paths. -/
def homotopySetoid
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (A →⋆ₙₐ[ℂ] B) where
  r := Homotopic
  iseqv := Homotopic.equivalence A B

/-- The actual ordinary homomorphism homotopy classes [A,B]. -/
abbrev HomotopyClasses
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  Quotient (homotopySetoid A B)

/-- The class of an actual star homomorphism in the point-norm homotopy quotient. -/
def mkHomotopyClass (f : A →⋆ₙₐ[ℂ] B) : HomotopyClasses A B :=
  Quotient.mk _ f

@[simp]
theorem mkHomotopyClass_eq_iff (f g : A →⋆ₙₐ[ℂ] B) :
    mkHomotopyClass f = mkHomotopyClass g ↔ Homotopic f g := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- Contravariant fixed-hom action on actual ordinary classes. -/
def precompClass (f : C →⋆ₙₐ[ℂ] A) :
    HomotopyClasses A B → HomotopyClasses C B :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid C B)
    (fun g => g.comp f) (by
    intro g h hgh
    exact Homotopic.precomp hgh f)

/-- Covariant fixed-hom action on actual ordinary classes. -/
def postcompClass (g : B →⋆ₙₐ[ℂ] C) :
    HomotopyClasses A B → HomotopyClasses A C :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid A C)
    (fun f => g.comp f) (by
    intro f h hfh
    exact Homotopic.postcomp hfh g)

@[simp]
theorem precompClass_mk (f : C →⋆ₙₐ[ℂ] A) (g : A →⋆ₙₐ[ℂ] B) :
    precompClass f (mkHomotopyClass g) = mkHomotopyClass (g.comp f) := by
  rfl

@[simp]
theorem postcompClass_mk (g : B →⋆ₙₐ[ℂ] C) (f : A →⋆ₙₐ[ℂ] B) :
    postcompClass g (mkHomotopyClass f) = mkHomotopyClass (g.comp f) := by
  rfl

end NonUnitalStarAlgHom

namespace AsymptoticMorphism

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

/-- Precompose by a fixed actual nonunital star hom.
No continuity or linearity of the asymptotic slice is added. -/
def precomp (φ : AsymptoticMorphism A B) (f : C →⋆ₙₐ[ℂ] A) :
    AsymptoticMorphism C B where
  toFun t a := φ t (f a)
  continuous_orbit a := φ.continuous_orbit (f a)
  add_defect_tendsto a b := by
    simpa only [toFun_eq_coe, map_add] using φ.add_defect_tendsto (f a) (f b)
  smul_defect_tendsto z a := by
    simpa only [toFun_eq_coe, map_smul] using φ.smul_defect_tendsto z (f a)
  mul_defect_tendsto a b := by
    simpa only [toFun_eq_coe, map_mul] using φ.mul_defect_tendsto (f a) (f b)
  star_defect_tendsto a := by
    simpa only [toFun_eq_coe, map_star] using φ.star_defect_tendsto (f a)

@[simp]
theorem precomp_apply (φ : AsymptoticMorphism A B) (f : C →⋆ₙₐ[ℂ] A)
    (t : AsymptoticTime) (a : C) : precomp φ f t a = φ t (f a) := by
  rfl

@[simp]
theorem precomp_id (φ : AsymptoticMorphism A B) :
    precomp φ (NonUnitalStarAlgHom.id ℂ A) = φ := by
  apply ext
  intro t a
  rw [precomp_apply]
  rfl

@[simp]
theorem postcomp_id (φ : AsymptoticMorphism A B) :
    postcomp φ (NonUnitalStarAlgHom.id ℂ B) = φ := by
  apply ext
  intro t a
  rw [postcomp_apply]
  rfl

theorem precomp_comp (φ : AsymptoticMorphism A B)
    (f : C →⋆ₙₐ[ℂ] A) (g : D →⋆ₙₐ[ℂ] C) :
    precomp (precomp φ f) g = precomp φ (f.comp g) := by
  apply ext
  intro t a
  simp only [precomp_apply, NonUnitalStarAlgHom.comp_apply]

theorem postcomp_comp (φ : AsymptoticMorphism A B)
    (g : B →⋆ₙₐ[ℂ] C) (h : C →⋆ₙₐ[ℂ] D) :
    postcomp (postcomp φ g) h = postcomp φ (h.comp g) := by
  apply ext
  intro t a
  simp only [postcomp_apply, NonUnitalStarAlgHom.comp_apply]

theorem postcomp_precomp (φ : AsymptoticMorphism A B)
    (f : C →⋆ₙₐ[ℂ] A) (g : B →⋆ₙₐ[ℂ] D) :
    postcomp (precomp φ f) g = precomp (postcomp φ g) f := by
  apply ext
  intro t a
  simp only [precomp_apply, postcomp_apply]

@[simp]
theorem precomp_ofHom (g : A →⋆ₙₐ[ℂ] B) (f : C →⋆ₙₐ[ℂ] A) :
    precomp (ofHom g) f = ofHom (g.comp f) := by
  apply ext
  intro t a
  simp only [precomp_apply, ofHom_apply, NonUnitalStarAlgHom.comp_apply]

@[simp]
theorem postcomp_ofHom (f : A →⋆ₙₐ[ℂ] B) (g : B →⋆ₙₐ[ℂ] C) :
    postcomp (ofHom f) g = ofHom (g.comp f) := by
  apply ext
  intro t a
  simp only [postcomp_apply, ofHom_apply, NonUnitalStarAlgHom.comp_apply]

namespace Homotopy

/-- Precompose the actual homotopy family by a fixed star hom. -/
def precomp {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (f : C →⋆ₙₐ[ℂ] A) : Homotopy (AsymptoticMorphism.precomp φ f)
      (AsymptoticMorphism.precomp ψ f) where
  family := AsymptoticMorphism.precomp H.family f
  start := by
    intro t a
    rw [precomp_apply, precomp_apply]
    exact H.start t (f a)
  finish := by
    intro t a
    rw [precomp_apply, precomp_apply]
    exact H.finish t (f a)

/-- Postcompose through the actual coefficient star hom on C([0,1],B). -/
def postcomp {φ ψ : AsymptoticMorphism A B} (H : Homotopy φ ψ)
    (g : B →⋆ₙₐ[ℂ] C) : Homotopy (AsymptoticMorphism.postcomp φ g)
      (AsymptoticMorphism.postcomp ψ g) where
  family := AsymptoticMorphism.postcomp H.family
    (ContinuousMap.compNonUnitalStarAlgHom unitInterval g)
  start := by
    intro t a
    rw [postcomp_apply, ContinuousMap.compNonUnitalStarAlgHom_apply, postcomp_apply]
    exact congrArg g (H.start t a)
  finish := by
    intro t a
    rw [postcomp_apply, ContinuousMap.compNonUnitalStarAlgHom_apply, postcomp_apply]
    exact congrArg g (H.finish t a)

end Homotopy

theorem homotopic_precomp {φ ψ : AsymptoticMorphism A B}
    (h : Homotopic φ ψ) (f : C →⋆ₙₐ[ℂ] A) :
    Homotopic (precomp φ f) (precomp ψ f) := by
  rcases h with ⟨H⟩
  exact ⟨H.precomp f⟩

theorem homotopic_postcomp {φ ψ : AsymptoticMorphism A B}
    (h : Homotopic φ ψ) (g : B →⋆ₙₐ[ℂ] C) :
    Homotopic (postcomp φ g) (postcomp ψ g) := by
  rcases h with ⟨H⟩
  exact ⟨H.postcomp g⟩

/-- An ordinary point-norm homotopy supplies a constant-in-time asymptotic
homotopy. The existing relation is an existential F, not a record assumed here. -/
theorem homotopic_ofHom {f g : A →⋆ₙₐ[ℂ] B}
    (h : NonUnitalStarAlgHom.Homotopic f g) : Homotopic (ofHom f) (ofHom g) := by
  rcases h with ⟨F, h0, h1⟩
  refine ⟨{ family := ofHom F, start := ?_, finish := ?_ }⟩
  · intro t a
    rw [ofHom_apply, ofHom_apply]
    exact h0 a
  · intro t a
    rw [ofHom_apply, ofHom_apply]
    exact h1 a

/-- Contravariant fixed-hom action on actual asymptotic homotopy classes. -/
def precompClass (f : C →⋆ₙₐ[ℂ] A) :
    HomotopyClasses A B → HomotopyClasses C B :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid C B)
    (fun φ => precomp φ f) (by
    intro φ ψ h
    exact homotopic_precomp h f)

/-- Covariant fixed-hom action on actual asymptotic homotopy classes. -/
def postcompClass (g : B →⋆ₙₐ[ℂ] C) :
    HomotopyClasses A B → HomotopyClasses A C :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid A C)
    (fun φ => postcomp φ g) (by
    intro φ ψ h
    exact homotopic_postcomp h g)

@[simp]
theorem precompClass_mk (f : C →⋆ₙₐ[ℂ] A) (φ : AsymptoticMorphism A B) :
    precompClass f (mkClass φ) = mkClass (precomp φ f) := by
  rfl

@[simp]
theorem postcompClass_mk (g : B →⋆ₙₐ[ℂ] C) (φ : AsymptoticMorphism A B) :
    postcompClass g (mkClass φ) = mkClass (postcomp φ g) := by
  rfl

/-- The actual natural map [A,B]->[[A,B]]. -/
def ofHomClass : NonUnitalStarAlgHom.HomotopyClasses A B → HomotopyClasses A B :=
  Quotient.map (sa := NonUnitalStarAlgHom.homotopySetoid A B)
    (sb := homotopySetoid A B) ofHom (by
    intro f g h
    exact homotopic_ofHom h)

@[simp]
theorem ofHomClass_mk (f : A →⋆ₙₐ[ℂ] B) :
    ofHomClass (NonUnitalStarAlgHom.mkHomotopyClass f) = mkClass (ofHom f) := by
  rfl

theorem precompClass_id (q : HomotopyClasses A B) :
    precompClass (NonUnitalStarAlgHom.id ℂ A) q = q := by
  refine Quotient.inductionOn q fun φ => ?_
  change precompClass (NonUnitalStarAlgHom.id ℂ A) (mkClass φ) = mkClass φ
  rw [precompClass_mk, precomp_id]

theorem postcompClass_id (q : HomotopyClasses A B) :
    postcompClass (NonUnitalStarAlgHom.id ℂ B) q = q := by
  refine Quotient.inductionOn q fun φ => ?_
  change postcompClass (NonUnitalStarAlgHom.id ℂ B) (mkClass φ) = mkClass φ
  rw [postcompClass_mk, postcomp_id]

theorem precompClass_comp (q : HomotopyClasses A B)
    (f : C →⋆ₙₐ[ℂ] A) (g : D →⋆ₙₐ[ℂ] C) :
    precompClass g (precompClass f q) = precompClass (f.comp g) q := by
  refine Quotient.inductionOn q fun φ => ?_
  change precompClass g (precompClass f (mkClass φ)) =
    precompClass (f.comp g) (mkClass φ)
  rw [precompClass_mk, precompClass_mk, precompClass_mk, precomp_comp]

theorem postcompClass_comp (q : HomotopyClasses A B)
    (g : B →⋆ₙₐ[ℂ] C) (h : C →⋆ₙₐ[ℂ] D) :
    postcompClass h (postcompClass g q) = postcompClass (h.comp g) q := by
  refine Quotient.inductionOn q fun φ => ?_
  change postcompClass h (postcompClass g (mkClass φ)) =
    postcompClass (h.comp g) (mkClass φ)
  rw [postcompClass_mk, postcompClass_mk, postcompClass_mk, postcomp_comp]

theorem postcompClass_precomp (q : HomotopyClasses A B)
    (f : C →⋆ₙₐ[ℂ] A) (g : B →⋆ₙₐ[ℂ] D) :
    postcompClass g (precompClass f q) = precompClass f (postcompClass g q) := by
  refine Quotient.inductionOn q fun φ => ?_
  change postcompClass g (precompClass f (mkClass φ)) =
    precompClass f (postcompClass g (mkClass φ))
  rw [precompClass_mk, postcompClass_mk, postcompClass_mk, precompClass_mk,
    postcomp_precomp]

theorem ofHomClass_precomp
    (q : NonUnitalStarAlgHom.HomotopyClasses A B) (f : C →⋆ₙₐ[ℂ] A) :
    ofHomClass (NonUnitalStarAlgHom.precompClass f q) =
      precompClass f (ofHomClass q) := by
  refine Quotient.inductionOn q fun g => ?_
  change ofHomClass (NonUnitalStarAlgHom.precompClass f
      (NonUnitalStarAlgHom.mkHomotopyClass g)) =
    precompClass f (ofHomClass (NonUnitalStarAlgHom.mkHomotopyClass g))
  rw [NonUnitalStarAlgHom.precompClass_mk, ofHomClass_mk, ofHomClass_mk,
    precompClass_mk, precomp_ofHom]

theorem ofHomClass_postcomp
    (q : NonUnitalStarAlgHom.HomotopyClasses A B) (g : B →⋆ₙₐ[ℂ] C) :
    ofHomClass (NonUnitalStarAlgHom.postcompClass g q) =
      postcompClass g (ofHomClass q) := by
  refine Quotient.inductionOn q fun f => ?_
  change ofHomClass (NonUnitalStarAlgHom.postcompClass g
      (NonUnitalStarAlgHom.mkHomotopyClass f)) =
    postcompClass g (ofHomClass (NonUnitalStarAlgHom.mkHomotopyClass f))
  rw [NonUnitalStarAlgHom.postcompClass_mk, ofHomClass_mk, ofHomClass_mk,
    postcompClass_mk, postcomp_ofHom]

end AsymptoticMorphism
