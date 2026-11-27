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

public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSNormalHom
public import MathlibExt.Analysis.VonNeumannAlgebra.Weight.GNSInjective
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.ImageEquiv

/-!
# Normal image equivalence of an NSF weight's GNS map

For a normal semifinite faithful weight `φ` on a concrete von Neumann algebra `M`, the GNS star
map `π : M → B(H_φ)` is a normal injective homomorphism.

Its operator range `π(M)` is a von Neumann algebra on `H_φ`. The resulting normal star
equivalence `M ≃ π(M)` has forward operator value `π(a)` and an ultraweakly continuous inverse.
The image is the range of this representation, not the full operator algebra in general.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Injectivity of the normal GNS map for an NSF weight.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an
extended positive weight: additive, homogeneous for finite nonnegative real scalars, and
zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into
the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume
`φ` preserves least upper bounds of nonempty norm-bounded directed positive sets. Assume
also that the complex span of finite-weight positive elements is ultraweakly dense and
that `φ(a)=0 → a=0` on positive elements. the normal homomorphism
`normalWeightGNSStarAlgHom M φ` is injective. -/
theorem normalSemifiniteFaithfulWeightGNSStarAlgHom_injective
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) :
    Function.Injective (normalWeightGNSStarAlgHom M φ.val φ.property.1) := by
  intro a b h
  apply φ.val.gnsLeftStarAlgHom_injective M φ.property.2.1 φ.property.2.2
  have hvalue := congrArg
    (fun T : (⊤ : VonNeumannAlgebra φ.val.GNS) => (T : φ.val.GNS →L[ℂ] φ.val.GNS)) h
  rw [normalWeightGNSStarAlgHom_apply, normalWeightGNSStarAlgHom_apply] at hvalue
  exact hvalue

/-- **Von Neumann operator image of an NSF GNS representation.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an
extended positive weight: additive, homogeneous for finite nonnegative real scalars, and
zero at zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into
the weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume
`φ` preserves least upper bounds of nonempty norm-bounded directed positive sets. Assume
also that the complex span of finite-weight positive elements is ultraweakly dense and
that `φ(a)=0 → a=0` on positive elements. `normalSemifiniteFaithfulWeightGNSImage M φ` is
the von Neumann algebra on `H_φ` with operator carrier `π(M)`. -/
def normalSemifiniteFaithfulWeightGNSImage
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) : VonNeumannAlgebra φ.val.GNS :=
  (normalWeightGNSStarAlgHom M φ.val φ.property.1).imageVonNeumannAlgebra
    (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ)

/-- **Normal equivalence onto an NSF GNS image.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into the
weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume `φ`
preserves least upper bounds of nonempty norm-bounded directed positive sets. Assume also
that the complex span of finite-weight positive elements is ultraweakly dense and that
`φ(a)=0 → a=0` on positive elements. `normalSemifiniteFaithfulWeightGNSImageEquiv M φ : M
≃ π(M)` is a complex star-algebra equivalence with both directions ultraweakly continuous
and forward map `a ↦ π(a)`. -/
def normalSemifiniteFaithfulWeightGNSImageEquiv
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) :
    NormalStarAlgEquiv M (normalSemifiniteFaithfulWeightGNSImage M φ) :=
  (normalWeightGNSStarAlgHom M φ.val φ.property.1).imageEquiv
    (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ)

/-- **Exact operator carrier of an NSF GNS image.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into the
weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume `φ`
preserves least upper bounds of nonempty norm-bounded directed positive sets. Assume also
that the complex span of finite-weight positive elements is ultraweakly dense and that
`φ(a)=0 → a=0` on positive elements. the set underlying
`normalSemifiniteFaithfulWeightGNSImage M φ` is `range(φ.gnsLeftStarAlgHom)=π(M)`. -/
theorem coe_normalSemifiniteFaithfulWeightGNSImage
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) :
    (normalSemifiniteFaithfulWeightGNSImage M φ : Set (φ.val.GNS →L[ℂ] φ.val.GNS)) =
      Set.range φ.val.gnsLeftStarAlgHom := by
  let f := normalWeightGNSStarAlgHom M φ.val φ.property.1
  change (f.imageVonNeumannAlgebra (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ) :
    Set (φ.val.GNS →L[ℂ] φ.val.GNS)) = Set.range φ.val.gnsLeftStarAlgHom
  rw [f.coe_imageVonNeumannAlgebra]
  simp only [f, normalWeightGNSStarAlgHom_apply]

/-- **Forward value of the NSF GNS normal equivalence.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. Put `n_φ={x : φ(x* x)<∞}`, and let `Λ : n_φ → H_φ` be the dense GNS map into the
weight Hilbert completion. Its representation `π` satisfies `π(a)Λ(x)=Λ(a*x)`. Assume `φ`
preserves least upper bounds of nonempty norm-bounded directed positive sets. Assume also
that the complex span of finite-weight positive elements is ultraweakly dense and that
`φ(a)=0 → a=0` on positive elements. for `a ∈ M`, the bounded operator underlying
`normalSemifiniteFaithfulWeightGNSImageEquiv M φ a` equals `φ.gnsLeftStarAlgHom a=π(a)`. -/
theorem normalSemifiniteFaithfulWeightGNSImageEquiv_apply
    (M : VonNeumannAlgebra H) (φ : NormalSemifiniteFaithfulWeight M) (a : M) :
    (normalSemifiniteFaithfulWeightGNSImageEquiv M φ a : φ.val.GNS →L[ℂ] φ.val.GNS) =
      φ.val.gnsLeftStarAlgHom a := by
  let f := normalWeightGNSStarAlgHom M φ.val φ.property.1
  have h := f.imageEquiv_apply (normalSemifiniteFaithfulWeightGNSStarAlgHom_injective M φ) a
  exact h.trans (normalWeightGNSStarAlgHom_apply M φ.val φ.property.1 a)

end

end VonNeumannAlgebra
