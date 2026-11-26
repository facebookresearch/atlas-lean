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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.CanonicalBaseChange

/-!
# Base change of right Hilbert modules

For nonunital C-star algebras `B,C` with star-compatible opposite orders, a complex nonunital
star homomorphism `f : B → C`, and a complete right Hilbert `B`-module `E`, form `E ⊗_f C` using
the left action `b c = f(b)*c` on the coefficient self-module `C`. Its pure inner product is
`⟨x⊗c,y⊗d⟩_C = star c * f(⟨x,y⟩_B) * d`.

The canonical map `j : E → E ⊗_f C` is characterized by `j(x) <• c = x⊗c` and `⟨j(x),j(y)⟩_C =
f(⟨x,y⟩_B)`; it is contractive. Adjointable endomorphisms act by `T(x)⊗c`, send rank-one maps to
rank-one maps of canonical images, and preserve module compacts. Countable generation of `E`
implies countable generation of the base change. Zero homomorphisms and nonunital coefficient
algebras are allowed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra CStarModule.Right RightActions

namespace CStarModule.InternalTensorProduct.BaseChange

universe uB uC uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {C : Type uC} [NonUnitalCStarAlgebra C]
  [PartialOrder Cᵐᵒᵖ] [StarOrderedRing Cᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- **Left coefficient action for base change.** For nonunital C-star algebras `B,C`, the right
self-module of `C` with star-compatible opposite order, and a complex nonunital star
homomorphism `f : B → C`, the representation sends `b` to the adjointable left multiplier `c ↦
f(b)*c`. -/
def coefficientAction (f : B →⋆ₙₐ[ℂ] C) : B →⋆ₙₐ[ℂ] AdjointableOperator.End C C :=
  (AdjointableOperator.leftRegular (B := C)).comp f

omit [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ] in
/-- **Value of the base-change coefficient action.** For a complex nonunital star homomorphism `f
: B → C` of C-star algebras and the right self-module of `C`, `coefficientAction f b c = f b *
c`. -/
@[simp]
theorem coefficientAction_apply (f : B →⋆ₙₐ[ℂ] C) (b : B) (c : C) :
    coefficientAction f b c = f b * c := rfl

/-- **Completed base-change module.** For nonunital C-star algebras `B,C` with star-compatible
opposite orders, a complete right `B`-module `E`, and a complex nonunital star homomorphism `f
: B → C`, `Carrier f` is the completed internal tensor `E ⊗_f C`, with the balancing relation
`(x <• b)⊗c = x⊗(f(b)*c)`. -/
abbrev Carrier (f : B →⋆ₙₐ[ℂ] C) := CompletedTensor (E₁ := E) (coefficientAction f)

/-- **Normed group of the base-change module.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, the completed module has the norm induced by `⟨x⊗c,y⊗d⟩_C = star c *
f(⟨x,y⟩_B) * d`. -/
@[instance_reducible]
def normedAddCommGroup (f : B →⋆ₙₐ[ℂ] C) : NormedAddCommGroup (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  exact inferInstance

attribute [local instance] normedAddCommGroup

/-- **Complex normed space of the base change.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, the complex scalar action on `E ⊗_f C` extends the balanced tensor
action, with its coefficient inner-product norm. -/
@[instance_reducible]
def normedSpace (f : B →⋆ₙₐ[ℂ] C) : NormedSpace ℂ (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  exact inferInstance

attribute [local instance] normedSpace

/-- **Right target-coefficient action after base change.** For nonunital C-star algebras `B,C`
with star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital
star homomorphism `f : B → C`, the continuous `C` action is determined by `(x⊗c) <• d =
x⊗(c*d)`. -/
@[instance_reducible]
def rightAction (f : B →⋆ₙₐ[ℂ] C) : SMul Cᵐᵒᵖ (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  letI : SMul Cᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalRightAction (coefficientAction f)
  exact inferInstance

attribute [local instance] rightAction

/-- **Right Hilbert-module structure after base change.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, the completed carrier is a right `C`-module with pure inner product
`star c * f(⟨x,y⟩_B) * d`. -/
@[instance_reducible]
def cstarModule (f : B →⋆ₙₐ[ℂ] C) : CStarModule Cᵐᵒᵖ (Carrier (E := E) f) := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  letI : SMul Cᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalRightAction (coefficientAction f)
  exact completedCStarModule (coefficientAction f)

attribute [local instance] cstarModule

/-- **Pure base-change tensor.** For nonunital C-star algebras `B,C` with star-compatible opposite
orders, a complete right `B`-module `E`, and a complex nonunital star homomorphism `f : B →
C`, `pure f x c` is the completed class of the balanced tensor `x⊗c`. -/
def pure (f : B →⋆ₙₐ[ℂ] C) (x : E) (c : C) : Carrier (E := E) f :=
  completedPure (coefficientAction f) x c

/-- **Internal tensor presentation of base change.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, the pure map `pure f` satisfies the bilinear, balancing, coefficient
inner-product and dense-span conditions of the completed internal tensor model. -/
theorem isModel (f : B →⋆ₙₐ[ℂ] C) : IsModel (coefficientAction f) (pure (E := E) f) := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedAddCommGroup (coefficientAction f)
  let : NormedSpace ℂ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalTensorNormedSpace (coefficientAction f)
  let : SMul Cᵐᵒᵖ (RadicalTensor (E₁ := E) (coefficientAction f)) :=
    radicalRightAction (coefficientAction f)
  exact completed_isModel (coefficientAction f)

/-- **Inner product of pure base-change tensors.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, `⟨pure f x c,pure f y d⟩_C = star c * f(⟨x,y⟩_B) * d`. -/
theorem pure_inner (f : B →⋆ₙₐ[ℂ] C) (x y : E) (c d : C) :
    CStarModule.rightInner (B := C) (pure f x c) (pure f y d) =
      star c * f (CStarModule.rightInner (B := B) x y) * d := by
  simpa only [coefficientAction_apply, CStarModule.Right.rightInner_self, mul_assoc] using
    (isModel (E := E) f).2.2.2.2.2.2.1 x y c d

/-- **Canonical vector map into base change.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, the continuous complex-linear map `j = canonicalMap f` satisfies
`j(x) <• c = pure f x c`, without requiring an identity in `C`. -/
def canonicalMap (f : B →⋆ₙₐ[ℂ] C) : E →L[ℂ] Carrier (E := E) f :=
  IsModel.canonicalBaseChangeMap (isModel (E := E) f)

/-- **Inner product of canonical base-change images.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, for `j = canonicalMap f`, `⟨j(x),j(y)⟩_C = f(⟨x,y⟩_B)`. -/
@[simp]
theorem canonicalMap_inner (f : B →⋆ₙₐ[ℂ] C) (x y : E) :
    CStarModule.rightInner (B := C) (canonicalMap f x) (canonicalMap f y) =
      f (CStarModule.rightInner (B := B) x y) :=
  IsModel.canonicalBaseChangeMap_inner (isModel (E := E) f) x y

/-- **Contractive canonical base-change map.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, `‖canonicalMap f x‖ ≤ ‖x‖`; injectivity of `f` is not a hypothesis. -/
theorem norm_canonicalMap_le (f : B →⋆ₙₐ[ℂ] C) (x : E) : ‖canonicalMap f x‖ ≤ ‖x‖ :=
  IsModel.norm_canonicalBaseChangeMap_le (isModel (E := E) f) x

/-- **Coefficient covariance of the canonical vector map.** For nonunital C-star algebras `B,C`
with star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital
star homomorphism `f : B → C`, `canonicalMap f (x <• b) = canonicalMap f x <• f b`. -/
@[simp]
theorem canonicalMap_right_smul (f : B →⋆ₙₐ[ℂ] C) (x : E) (b : B) :
    canonicalMap f (x <• b) = canonicalMap f x <• f b :=
  IsModel.canonicalBaseChangeMap_right_smul (isModel (E := E) f) x b

/-- **Pure tensors from canonical images.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, `canonicalMap f x <• c = pure f x c` for all `x : E`, `c : C`. -/
@[simp]
theorem canonicalMap_pure (f : B →⋆ₙₐ[ℂ] C) (x : E) (c : C) :
    canonicalMap f x <• c = pure f x c :=
  IsModel.canonicalBaseChangeMap_pure (isModel (E := E) f) x c

/-- **Adjointable endomorphism base change.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, the unital star-algebra homomorphism on endomorphisms is determined
by `T(x⊗c) = (T x)⊗c`. -/
def endomorphismMap (f : B →⋆ₙₐ[ℂ] C) : AdjointableOperator.End B E →⋆ₐ[ℂ]
    AdjointableOperator.End C (Carrier (E := E) f) :=
  IsModel.mapLeftStarAlgHom (isModel (E := E) f)

/-- **Base-changed endomorphism on a pure tensor.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, `endomorphismMap f T (pure f x c) = pure f (T x) c`. -/
@[simp]
theorem endomorphismMap_pure (f : B →⋆ₙₐ[ℂ] C) (T : AdjointableOperator.End B E)
    (x : E) (c : C) : endomorphismMap f T (pure f x c) = pure f (T x) c :=
  IsModel.mapLeftStarAlgHom_pure (isModel (E := E) f) T x c

/-- **Endomorphisms on canonical vector images.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, `endomorphismMap f T (canonicalMap f x) = canonicalMap f (T x)`. -/
@[simp]
theorem endomorphismMap_canonicalMap (f : B →⋆ₙₐ[ℂ] C) (T : AdjointableOperator.End B E)
    (x : E) : endomorphismMap f T (canonicalMap f x) = canonicalMap f (T x) :=
  IsModel.mapLeftStarAlgHom_canonicalBaseChangeMap (isModel (E := E) f) T x

/-- **Rank-one maps under base change.** For nonunital C-star algebras `B,C` with star-compatible
opposite orders, a complete right `B`-module `E`, and a complex nonunital star homomorphism `f
: B → C`, the image of the module rank-one map `θ_(x,y)` is `θ_(canonicalMap f x, canonicalMap
f y)`. -/
theorem endomorphismMap_rankOne (f : B →⋆ₙₐ[ℂ] C) (x y : E) :
    endomorphismMap f (AdjointableOperator.rankOne (B := B) x y) =
      AdjointableOperator.rankOne (B := C) (canonicalMap f x) (canonicalMap f y) :=
  IsModel.mapLeftStarAlgHom_rankOne_baseChange (isModel (E := E) f) x y

/-- **Module compacts under base change.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, if `T` is module-compact on `E`, then `endomorphismMap f T` is
module-compact on `E ⊗_f C`. -/
theorem endomorphismMap_mem_compact (f : B →⋆ₙₐ[ℂ] C) {T : AdjointableOperator.End B E}
    (hT : T ∈ AdjointableOperator.compactSubmodule (B := B) (E := E) (F := E)) :
    endomorphismMap f T ∈ AdjointableOperator.compactSubmodule
      (B := C) (E := Carrier (E := E) f) (F := Carrier (E := E) f) :=
  IsModel.mapLeftStarAlgHom_mem_compact_baseChange (isModel (E := E) f) hT

/-- **Countable generation under base change.** For nonunital C-star algebras `B,C` with
star-compatible opposite orders, a complete right `B`-module `E`, and a complex nonunital star
homomorphism `f : B → C`, if `E` is countably generated, then `E ⊗_f C` is countably generated
by the canonical images of its generators. -/
theorem countablyGenerated (f : B →⋆ₙₐ[ℂ] C)
    (hE : CStarModule.IsCountablyGenerated (B := B) (E := E)) :
    CStarModule.IsCountablyGenerated (B := C) (E := Carrier (E := E) f) :=
  IsModel.countablyGenerated_baseChange (isModel (E := E) f) hE

end CStarModule.InternalTensorProduct.BaseChange
