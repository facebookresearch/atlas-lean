/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.CompletelyPositiveHomotopyEquivalence
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Functoriality

/-!
# Star-homomorphism functoriality of CP-contractive families

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. For a nonunital complex star homomorphism f:C→A, precomposition has values
φ_t(f(c)); for g:B→C, postcomposition has values g(φ_t(a)). These actions preserve
CP-contractive interval-valued homotopies and induce the corresponding maps on their homotopy
classes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace AsymptoticMorphism
namespace CompletelyPositiveContraction

universe uA uB uC

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- **Precomposition of a CP-contractive family.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. For a nonunital complex star homomorphism f:C→A,
CompletelyPositiveContraction.precomp φ f:C→B has values (φ∘f)_t(c)=φ_t(f(c)) and completely
positive contraction slices.
-/
noncomputable def precomp (phi : CompletelyPositiveContraction A B)
    (f : C →⋆ₙₐ[ℂ] A) : CompletelyPositiveContraction C B where
  toAsymptoticMorphism :=
    AsymptoticMorphism.precomp phi.toAsymptoticMorphism f
  completelyPositiveContraction := by
    let _ : PartialOrder C := CStarAlgebra.spectralOrder C
    let _ : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
    let _ : PartialOrder A := CStarAlgebra.spectralOrder A
    let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
    let _ : PartialOrder B := CStarAlgebra.spectralOrder B
    let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    have hphi := phi.completelyPositiveContraction
    dsimp only [IsCompletelyPositiveContraction] at hphi ⊢
    intro t
    obtain ⟨s, hsNorm, hsValue⟩ := hphi t
    let fCP : C →CP A :=
      CompletelyPositiveMapClass.toCompletelyPositiveLinearMap f
    let sf : C →CP B := CompletelyPositiveMap.comp s fCP
    refine ⟨sf, ?_, ?_⟩
    · intro c
      calc
        ‖sf c‖ = ‖s (f c)‖ := rfl
        _ ≤ ‖f c‖ := hsNorm (f c)
        _ ≤ ‖c‖ := NonUnitalStarAlgHom.norm_apply_le f c
    · intro c
      change s (f c) = phi.toAsymptoticMorphism t (f c)
      exact hsValue (f c)

/-- **Underlying family of CP-contractive precomposition.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. For a nonunital complex star homomorphism f:C→A, the underlying asymptotic family of
φ.precomp f equals AsymptoticMorphism.precomp φ.toAsymptoticMorphism f.
-/
@[simp]
theorem precomp_toAsymptoticMorphism
    (phi : CompletelyPositiveContraction A B) (f : C →⋆ₙₐ[ℂ] A) :
    (precomp phi f).toAsymptoticMorphism =
      AsymptoticMorphism.precomp phi.toAsymptoticMorphism f :=
  rfl

/-- **Value of CP-contractive precomposition.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. For a nonunital complex star homomorphism f:C→A, t≥1 and c∈C, (φ.precomp
f)_t(c)=φ_t(f(c)).
-/
theorem precomp_apply
    (phi : CompletelyPositiveContraction A B) (f : C →⋆ₙₐ[ℂ] A)
    (t : AsymptoticTime) (c : C) :
    (precomp phi f).toAsymptoticMorphism t c =
      phi.toAsymptoticMorphism t (f c) :=
  rfl

namespace Homotopy

variable {phi psi : CompletelyPositiveContraction A B}

/-- **Precomposition of a CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. If C is a nonunital complex C-star algebra and f:C→A a nonunital complex star
homomorphism, Homotopy.precomp H f joins φ∘f to ψ∘f with family H_t(f(c))(s).
-/
noncomputable def precomp (H : Homotopy phi psi)
    (f : C →⋆ₙₐ[ℂ] A) : Homotopy (phi.precomp f) (psi.precomp f) where
  family := H.family.precomp f
  start := by
    intro t c
    rw [CompletelyPositiveContraction.precomp_apply,
      CompletelyPositiveContraction.precomp_apply]
    exact H.start t (f c)
  finish := by
    intro t c
    rw [CompletelyPositiveContraction.precomp_apply,
      CompletelyPositiveContraction.precomp_apply]
    exact H.finish t (f c)

/-- **Postcomposition of a CP-contractive homotopy.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. If C is a nonunital complex C-star algebra and g:B→C a nonunital complex star
homomorphism, Homotopy.postcomp H g joins g∘φ to g∘ψ with family g(H_t(a)(s)).
-/
noncomputable def postcomp (H : Homotopy phi psi)
    (g : B →⋆ₙₐ[ℂ] C) : Homotopy (phi.postcomp g) (psi.postcomp g) where
  family := H.family.postcomp
    (ContinuousMap.compNonUnitalStarAlgHom unitInterval g)
  start := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply,
      ContinuousMap.compNonUnitalStarAlgHom_apply,
      CompletelyPositiveContraction.postcomp_apply]
    exact congrArg g (H.start t a)
  finish := by
    intro t a
    rw [CompletelyPositiveContraction.postcomp_apply,
      ContinuousMap.compNonUnitalStarAlgHom_apply,
      CompletelyPositiveContraction.postcomp_apply]
    exact congrArg g (H.finish t a)

/-- **Underlying asymptotic homotopy of CP precomposition.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. For a nonunital complex star homomorphism f:C→A from a nonunital complex C-star
algebra, the ordinary asymptotic homotopy underlying H.precomp f equals
H.toAsymptoticHomotopy.precomp f.
-/
@[simp]
theorem precomp_toAsymptoticHomotopy
    (H : Homotopy phi psi) (f : C →⋆ₙₐ[ℂ] A) :
    (precomp H f).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.precomp
        H.toAsymptoticHomotopy f := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

/-- **Underlying asymptotic homotopy of CP postcomposition.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. For a nonunital complex star homomorphism g:B→C into a nonunital complex C-star
algebra, the ordinary asymptotic homotopy underlying H.postcomp g equals
H.toAsymptoticHomotopy.postcomp g.
-/
@[simp]
theorem postcomp_toAsymptoticHomotopy
    (H : Homotopy phi psi) (g : B →⋆ₙₐ[ℂ] C) :
    (postcomp H g).toAsymptoticHomotopy =
      _root_.AsymptoticMorphism.Homotopy.postcomp
        H.toAsymptoticHomotopy g := by
  apply _root_.AsymptoticMorphism.Homotopy.ext
  rfl

end Homotopy

/-- **CP homotopy is preserved by source precomposition.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. If φ and ψ are CP-contractively homotopic and f:C→A is a nonunital complex star
homomorphism from a nonunital complex C-star algebra, then φ∘f and ψ∘f are CP-contractively
homotopic.
-/
theorem homotopic_precomp {phi psi : CompletelyPositiveContraction A B}
    (h : Homotopic phi psi) (f : C →⋆ₙₐ[ℂ] A) :
    Homotopic (phi.precomp f) (psi.precomp f) := by
  rcases h with ⟨H⟩
  exact ⟨H.precomp f⟩

/-- **CP homotopy is preserved by target postcomposition.**

Let A,B be nonunital complex C-star algebras and T=[1,∞). A CP-contractive asymptotic morphism
φ:A→B has continuous coefficient time orbits, vanishing algebraic defects at infinity, and
completely positive complex-linear slices with ‖φ_t(a)‖≤‖a‖. For such families φ,ψ, a homotopy
H is a CP-contractive asymptotic morphism A→C([0,1],B) with H_t(a)(0)=φ_t(a) and
H_t(a)(1)=ψ_t(a); its contraction bounds and defect limits use the supremum norm over the
interval. If φ and ψ are CP-contractively homotopic and g:B→C is a nonunital complex star
homomorphism into a nonunital complex C-star algebra, then g∘φ and g∘ψ are CP-contractively
homotopic.
-/
theorem homotopic_postcomp {phi psi : CompletelyPositiveContraction A B}
    (h : Homotopic phi psi) (g : B →⋆ₙₐ[ℂ] C) :
    Homotopic (phi.postcomp g) (psi.postcomp g) := by
  rcases h with ⟨H⟩
  exact ⟨H.postcomp g⟩

/-- **Precomposition on CP-contractive homotopy classes.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. Let Qcp(A,B) be the quotient of CP-contractive asymptotic morphisms by homotopies
through CP-contractive interval-valued families, and Qraw(A,B) the quotient of all asymptotic
star morphisms by their interval-valued asymptotic homotopies. For a nonunital complex star
homomorphism f:C→A, precompClass f:Qcp(A,B)→Qcp(C,B) sends [φ] to [φ∘f].
-/
def precompClass (f : C →⋆ₙₐ[ℂ] A) :
    HomotopyClasses A B → HomotopyClasses C B :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid C B)
    (fun phi => phi.precomp f) (by
      intro phi psi h
      exact homotopic_precomp h f)

/-- **Postcomposition on CP-contractive homotopy classes.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. Let Qcp(A,B) be the quotient of CP-contractive asymptotic morphisms by homotopies
through CP-contractive interval-valued families, and Qraw(A,B) the quotient of all asymptotic
star morphisms by their interval-valued asymptotic homotopies. For a nonunital complex star
homomorphism g:B→C, postcompClass g:Qcp(A,B)→Qcp(A,C) sends [φ] to [g∘φ].
-/
def postcompClass (g : B →⋆ₙₐ[ℂ] C) :
    HomotopyClasses A B → HomotopyClasses A C :=
  Quotient.map (sa := homotopySetoid A B) (sb := homotopySetoid A C)
    (fun phi => phi.postcomp g) (by
      intro phi psi h
      exact homotopic_postcomp h g)

/-- **Precomposition of a representative CP class.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. For a nonunital complex star homomorphism f:C→A, precompClass f (mkClass
φ)=mkClass(φ.precomp f), where mkClass denotes the CP-contractive homotopy class.
-/
@[simp]
theorem precompClass_mk
    (f : C →⋆ₙₐ[ℂ] A) (phi : CompletelyPositiveContraction A B) :
    precompClass f (mkClass phi) = mkClass (phi.precomp f) :=
  rfl

/-- **Postcomposition of a representative CP class.**

Let A,B,C be nonunital complex C-star algebras, T=[1,∞), and φ:A→B a CP-contractive asymptotic
morphism. For a nonunital complex star homomorphism g:B→C, postcompClass g (mkClass
φ)=mkClass(φ.postcomp g), where mkClass denotes the CP-contractive homotopy class.
-/
@[simp]
theorem postcompClass_mk
    (g : B →⋆ₙₐ[ℂ] C) (phi : CompletelyPositiveContraction A B) :
    postcompClass g (mkClass phi) = mkClass (phi.postcomp g) :=
  rfl

end CompletelyPositiveContraction
end AsymptoticMorphism
