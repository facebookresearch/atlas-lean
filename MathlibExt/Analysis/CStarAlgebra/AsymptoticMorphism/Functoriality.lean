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
# Functoriality of homotopy classes under star homomorphisms

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. Ordinary homomorphisms f,g:A→B are
point-norm homotopic when there is a nonunital complex star homomorphism F:A→C([0,1],B) with
F(a)(0)=f(a) and F(a)(1)=g(a). Precomposition by f:C→A and postcomposition by g:B→C act on
ordinary homotopy classes [A,B] and on asymptotic homotopy classes [[A,B]]. The constant
family φ_t(a)=h(a) of a star homomorphism h:A→B gives a map [A,B]→[[A,B]].
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

/-- **Setoid of point-norm homomorphism homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). Ordinary homomorphisms f,g:A→B are
point-norm homotopic when there is a nonunital complex star homomorphism F:A→C([0,1],B) with
F(a)(0)=f(a) and F(a)(1)=g(a). This is the equivalence relation in
NonUnitalStarAlgHom.homotopySetoid A B.
-/
def homotopySetoid
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    Setoid (A →⋆ₙₐ[ℂ] B) where
  r := Homotopic
  iseqv := Homotopic.equivalence A B

/-- **Ordinary star-homomorphism homotopy classes.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). Ordinary homomorphisms f,g:A→B are
point-norm homotopic when there is a nonunital complex star homomorphism F:A→C([0,1],B) with
F(a)(0)=f(a) and F(a)(1)=g(a). NonUnitalStarAlgHom.HomotopyClasses A B is the quotient of
nonunital complex star homomorphisms A→B by this relation, denoted [A,B].
-/
abbrev HomotopyClasses
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :=
  Quotient (homotopySetoid A B)

/-- **Homotopy class of a star homomorphism.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). Ordinary homomorphisms f,g:A→B are
point-norm homotopic when there is a nonunital complex star homomorphism F:A→C([0,1],B) with
F(a)(0)=f(a) and F(a)(1)=g(a). For a nonunital complex star homomorphism f:A→B,
mkHomotopyClass f is its class in [A,B].
-/
def mkHomotopyClass (f : A →⋆ₙₐ[ℂ] B) : HomotopyClasses A B :=
  Quotient.mk _ f

@[simp]
theorem mkHomotopyClass_eq_iff (f g : A →⋆ₙₐ[ℂ] B) :
    mkHomotopyClass f = mkHomotopyClass g ↔ Homotopic f g := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- **Precomposition on ordinary homomorphism classes.**

Let A,B,C be nonunital complex C-star algebras and f:C→A a nonunital complex star
homomorphism. On point-norm homotopy classes, NonUnitalStarAlgHom.precompClass f:[A,B]→[C,B]
sends [h] to [h∘f].
-/
def precompClass (f : C →⋆ₙₐ[ℂ] A) :
    HomotopyClasses A B → HomotopyClasses C B :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid C B)
    (fun g => g.comp f) (by
    intro g h hgh
    exact Homotopic.precomp hgh f)

/-- **Postcomposition on ordinary homomorphism classes.**

Let A,B,C be nonunital complex C-star algebras and g:B→C a nonunital complex star
homomorphism. On point-norm homotopy classes, NonUnitalStarAlgHom.postcompClass g:[A,B]→[A,C]
sends [h] to [g∘h].
-/
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

/-- **Fixed-homomorphism precomposition of an asymptotic family.**

Let A,B,C be nonunital complex C-star algebras, φ:A→B an asymptotic star morphism on T=[1,∞)
and f:C→A a nonunital complex star homomorphism. The family precomp φ f has values
(φ∘f)_t(c)=φ_t(f(c)).
-/
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

/-- **Precomposition of a whole asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. Let C be a nonunital
complex C-star algebra and f:C→A a nonunital complex star homomorphism. Homotopy.precomp H f
runs between φ∘f and ψ∘f, with interval-valued family c↦H_t(f(c)).
-/
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

/-- **Postcomposition of a whole asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). An asymptotic star morphism φ:A→B is
a family φ_t with continuous fixed-coefficient time orbits and four additive, scalar,
multiplicative and star defects tending to zero as t→∞. A homotopy H between asymptotic
families φ,ψ is an asymptotic family A→C([0,1],B) with H_t(a)(0)=φ_t(a) and H_t(a)(1)=ψ_t(a),
using the supremum norm for time continuity and all defect limits. Let C be a nonunital
complex C-star algebra and g:B→C a nonunital complex star homomorphism. Homotopy.postcomp H g
runs between g∘φ and g∘ψ, with values g(H_t(a)(s)).
-/
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

/-- **A point-norm homotopy gives a constant-time asymptotic homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). Ordinary homomorphisms f,g:A→B are
point-norm homotopic when there is a nonunital complex star homomorphism F:A→C([0,1],B) with
F(a)(0)=f(a) and F(a)(1)=g(a). If f,g are homotopic ordinary star homomorphisms, their
constant-time asymptotic families ofHom f and ofHom g are asymptotically homotopic: the same
path F is used at every t≥1.
-/
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

/-- **Precomposition on asymptotic homotopy classes.**

Let A,B,C be nonunital complex C-star algebras and f:C→A a nonunital complex star
homomorphism. The map AsymptoticMorphism.precompClass f:[[A,B]]→[[C,B]] sends [φ] to
[t↦φ_t∘f], where classes use homotopies with supremum-norm interval-valued defects.
-/
def precompClass (f : C →⋆ₙₐ[ℂ] A) :
    HomotopyClasses A B → HomotopyClasses C B :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid C B)
    (fun φ => precomp φ f) (by
    intro φ ψ h
    exact homotopic_precomp h f)

/-- **Postcomposition on asymptotic homotopy classes.**

Let A,B,C be nonunital complex C-star algebras and g:B→C a nonunital complex star
homomorphism. The map AsymptoticMorphism.postcompClass g:[[A,B]]→[[A,C]] sends [φ] to
[t↦g∘φ_t], with classes defined by supremum-norm interval-valued homotopies.
-/
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

/-- **Map from ordinary to asymptotic homotopy classes.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). The map ofHomClass:[A,B]→[[A,B]]
sends the point-norm homotopy class of a nonunital complex star homomorphism f:A→B to the
asymptotic homotopy class of the constant family φ_t(a)=f(a).
-/
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
