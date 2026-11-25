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

public import MathlibExt.Algebra.Homology.TwistingConvolutionLaws
public import MathlibExt.Algebra.Homology.TensorUnitor

/-!
# Convolution monoid laws

Built on `TwistingConvolutionLaws.lean`. This file proves the
dependency-closed infrastructure plus the three public laws
`CochainComplex.conv_assoc`, `CochainComplex.conv_one_left`, and
`CochainComplex.conv_one_right`. No `conv`/`convOne` redefinition, no `Monoid`
instance, and no
bar/cobar/totalization/EZ-AW/Koszul/operad/model-category material.

## Sources and conventions

Standard reference: Loday–Vallette, *Algebraic Operads*, Grundlehren 346
(2012), convolution `μ ∘ (f ⊗ g) ∘ Δ`; signs via pinned `up ℤ`
(`ComplexShape.ε_up_ℤ`) and `HomComplex.δ_comp` as implemented in
`TwistingCochain.lean`. Exact printed
section/sign match not verified; none claimed. See
`MathlibExt/RingTheory/DifferentialGraded/TwistingCochain.lean` for the full
convention map and `TwistingConvolutionLaws.lean` for `tensorCochain_assoc`,
`conv_leibniz`, and `convOne`.

## Declaration inventory

* `conv_eq` (private): `conv` unfolded to heterogeneous `Cochain.tensor`
  via `tensorCochain_eq_tensor`, for reuse by the associativity and unit
  proofs below.
* `convOne_vanish` (private): `convOne` vanishes in nonzero degree (factors
  through the tensor-unit graded object, `isZero_single_obj_X`).
* `tensor_comp_tensor_three` (private): triple interchange through
  heterogeneous tensors by double `tensor_comp_tensor`, with combined Koszul
  sign; reusable in the associativity proof below.
* `conv_one_left_transport` (private): verified cochain-level left-unit
  ingredients (slide components, unit-degree interchange, graded unitor,
  cast computation) for the surviving degree-zero summand, consumed by
  `conv_one_left` below.
* `conv_one_left` (public): convolution left unit up to `zero_add` transport,
  via the one-sided middle interchange plus inner support-collapse of
  `tensor (ofHom one) f` and the `ModuleCat` unitor assembly
  (`ιTensorObj_tensorHom`, `ιTensorObj_leftUnitor_hom`, unitor naturality).
* `conv_one_right` (public): mirror right unit up to `add_zero` transport.

## Unit-law proof path (both sides closed)

Each side factors `tensor convOne f` / `tensor f convOne` through the
one-sided middle interchange (`ofHom_tensorHom_comp_tensor` at unit degrees),
collapses the inner `tensor (ofHom one)` to its degree-zero survivor
(`one_vanish_general` kills every nonzero summand), and closes the surviving
`ModuleCat` composite with the generator formulas from `TensorUnitor`
(`ιTensorObj_tensorHom`, `ιTensorObj_leftUnitor_hom` /
`ιTensorObj_rightUnitor_hom`) plus unitor naturality. No new associativity
beyond the existing `conv_assoc`, no bar-cobar/twisting adjunctions.

## Nonclaims

No homological (`down ℤ`) API, bar–cobar
adjunction, twisting bijection, totalization, EZ/AW, derived/Koszul,
operadic, or model-categorical result; no public unitor/cast bridge beyond the
two unit transports above.

## Import justification

`TwistingConvolutionLaws` supplies `conv`/`convOne`/`tensorCochain_eq_tensor`
and the graded tensor/chain-map API transitively; `TensorUnitor` supplies the
generator formulas (`ιTensorObj_tensorHom`, `ιTensorObj_leftUnitor_hom`,
`ιTensorObj_rightUnitor_hom`) consumed by the unit bridges; no bar/cobar
imports.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [MonObj A] [ComonObj C]

/-- `conv` unfolded to heterogeneous `Cochain.tensor` via
`tensorCochain_eq_tensor`, for reuse by the associativity and unit proofs below. -/
private theorem conv_eq {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) :
    conv f g =
    ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))).comp
    (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero (m + n)) := by
  unfold conv
  rw [tensorCochain_eq_tensor]

/-- `convOne` vanishes in nonzero degree: it factors as counit followed by
unit through the tensor-unit graded object, which is zero away from `0`
(`isZero_single_obj_X`). Used by the unit support-collapse lemmas below. -/
private theorem convOne_vanish (i : ℤ) (hi : i ≠ 0) :
    (convOne (R := R) (C := C) (A := A)).v i i (by omega) = 0 := by
  unfold convOne
  simp only [HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v]
  have h0 : IsZero
      ((HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).X i) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat R)) i hi
  have hf0 : (ComonObj.counit (X := C)).f i = 0 := h0.eq_of_tgt _ _
  rw [hf0, zero_comp]

/-- General support-collapse form of `convOne_vanish` for arbitrary target degree.

For `convOne : Cochain C A 0`, the component at `(i, j)` with `i + 0 = j`
vanishes whenever `i ≠ 0`. This is the smallest reusable bridge after
`convOne_vanish`: heterogeneous tensor sums for `tensor convOne f` present
general `(i₁, j)` indices, not just the diagonal `(i, i)`, so each summand
with `i₁ ≠ 0` closes by this lemma before the one-sided interchange
(`ofHom_tensorHom_comp_tensor` / `tensor_comp_ofHom_tensorHom`), the
`counit_comul_hom` / `one_mul_hom` slides (`ofHom_counit_slide` /
`ofHom_one_slide`), the cochain-level unitor transport lifting
`leftUnitor'_inv`, and the degree cast `cochain_cast_v`.

Consumed by `conv_one_left` and `conv_one_right` below via the APIs above. -/
private theorem convOne_vanish_general (i j : ℤ) (hij : i + (0 : ℤ) = j)
    (hi : i ≠ 0) :
    (convOne (R := R) (C := C) (A := A)).v i j hij = 0 := by
  have hj : i = j := by omega
  subst hj
  exact convOne_vanish i hi

/-- Vanishing of non-degree-zero summands in `tensor convOne f`.

For `f : HomComplex.Cochain C A n`, the `(i₁, i₂)`-summand of
`HomComplex.Cochain.tensor convOne f` carries `convOne.v i₁ _ _`, which is
`0` when `i₁ ≠ 0` by `convOne_vanish_general`. Hence the signed tensor factor
vanishes. This is the descent half of reducing `tensor convOne f` to its
`i₁ = 0` summand; the `mapBifunctorDesc`-to-singleton identification, the
one-sided composition interchange, and the final unitor-around-`f`
identification are consumed by `conv_one_left` below. No
`IsComonHom`/`IsMonHom` hypothesis is introduced. -/
private theorem tensor_convOne_summand_vanish {n : ℤ}
    (f : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₁ : i₁ ≠ 0) :
    (n * i₁).negOnePow •
      ((convOne (R := R) (C := C) (A := A)).v i₁ (i₁ + 0) rfl ⊗ₘ
        f.v i₂ (i₂ + n) rfl) = 0 := by
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₁ (i₁ + 0) rfl = 0 :=
    convOne_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

/-- Support collapse of `tensor convOne f` to its surviving `i₁ = 0` summand.

For `f : HomComplex.Cochain C A n`, precomposing
`(HomComplex.Cochain.tensor convOne f).v r s hrs` with the `(i₁, i₂)`-inclusion
vanishes whenever `i₁ ≠ 0`: `ι_mapBifunctorDesc` identifies the component with
the signed summand, which is `0` by `tensor_convOne_summand_vanish`. Hence the
desc is determined by its `i₁ = 0` (`i₂ = r`) summand; the singleton
identification of the desc itself, the one-sided composition interchange
(pinned `ofHom_tensorHom_comp_tensor`, instantiated in
`conv_one_left_transport`), and the final unitor-around-`f` identification
are consumed by `conv_one_left` below. No `IsComonHom`/`IsMonHom`
hypothesis is introduced. -/
private theorem tensor_convOne_support_collapse {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₁ : i₁ ≠ 0) :
    HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₁ (i₁ + 0) rfl = 0 :=
    convOne_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

/-- Singleton-desc identification for `tensor convOne f`.

For `f : HomComplex.Cochain C A n`, every `(i₁, i₂)`-component of
`(HomComplex.Cochain.tensor convOne f).v r s hrs` is determined by the
surviving `i₁ = 0` summand: it vanishes when `i₁ ≠ 0` by
`tensor_convOne_support_collapse`, and at `(0, r)` it equals the explicit
signed summand (whose sign is `(n * 0).negOnePow`). This packages the descent
half of the left-unit reduction; the one-sided composition interchange
(instantiated in `conv_one_left_transport`), the `counit_comul_hom` /
`one_mul_hom` slides (`ofHom_counit_slide` / `ofHom_one_slide`), and the final
unitor-around-`f` identification are consumed by `conv_one_left` below. No
`IsComonHom`/`IsMonHom` hypothesis is introduced. -/
private theorem tensor_convOne_desc_singleton {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    (HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) 0 r r (zero_add r) ≫
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f).v
        r s hrs =
      (n * 0).negOnePow •
        ((convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl ⊗ₘ
          f.v r (r + n) rfl) ≫
        HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₁ : i₁ ≠ 0),
      HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₁ => tensor_convOne_support_collapse f r s hrs i₁ i₂ hij hi₁⟩

/-- Vanishing of non-degree-zero summands in `tensor f convOne` (right-unit mirror).

For `f : HomComplex.Cochain C A n`, the `(i₁, i₂)`-summand of
`HomComplex.Cochain.tensor f convOne` carries `convOne.v i₂ _ _`, which is
`0` when `i₂ ≠ 0` by `convOne_vanish_general`. The Koszul sign is
`(0 * i₁).negOnePow` (second factor has degree `0`), hence trivially `1`;
no braiding hypothesis is needed. This is the first descent step toward
reducing `tensor f convOne` to its `i₂ = 0` summand.

Reuses the left-unit architecture only where the degree-zero sign is valid.
Consumed by `conv_one_right` below together with the support collapse to the
`i₂ = 0` summand, the desc-to-singleton identification, the one-sided
composition interchange, the cochain-level `comul_counit` / `mul_one` slides
lifting `(ρ_ C).inv` / `(ρ_ A).hom`, and the right-unitor transport lifting
`rightUnitor'_inv` with degree cast `cochain_cast_v` at `add_zero n`. No
`IsComonHom`/`IsMonHom` or stronger monoid/comonoid hypothesis is
introduced. -/
private theorem tensor_f_convOne_summand_vanish {n : ℤ}
    (f : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₂ : i₂ ≠ 0) :
    (0 * i₁).negOnePow •
      (f.v i₁ (i₁ + n) rfl ⊗ₘ
        (convOne (R := R) (C := C) (A := A)).v i₂ (i₂ + 0) rfl) = 0 := by
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₂ (i₂ + 0) rfl = 0 :=
    convOne_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

/-- Support collapse of `tensor f convOne` to its surviving `i₂ = 0` summand.

For `f : HomComplex.Cochain C A n`, precomposing
`(HomComplex.Cochain.tensor f convOne).v r s hrs` with the `(i₁, i₂)`-inclusion
vanishes whenever `i₂ ≠ 0`: `ι_mapBifunctorDesc` identifies the component with
the signed summand, which is `0` by `tensor_f_convOne_summand_vanish`. Hence the
desc is determined by its `i₂ = 0` (`i₁ = r`) summand; the singleton
identification of the desc itself, the one-sided composition interchange, and
the final right-unitor-around-`f` identification are consumed by
`conv_one_right` below.

Index/order check: the surviving inclusion is `(r, 0)` via `add_zero r` (not
`(0, r)`), since `i₁ + i₂ = r` with `i₂ = 0` forces `i₁ = r`. Sign check: the
summand sign is `(0 * i₁).negOnePow` (second factor has degree `0`), hence
trivially `1` on the survivor; no braiding hypothesis is needed. Reuses only
pinned `tensor_v` and `ι_mapBifunctorDesc`, mirroring
`tensor_convOne_support_collapse`. No `IsComonHom`/`IsMonHom` hypothesis is
introduced. -/
private theorem tensor_f_convOne_support_collapse {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₂ : i₂ ≠ 0) :
    HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A))).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (convOne (R := R) (C := C) (A := A)).v i₂ (i₂ + 0) rfl = 0 :=
    convOne_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

/-- Singleton-desc identification for `tensor f convOne`.

For `f : HomComplex.Cochain C A n`, every `(i₁, i₂)`-component of
`(HomComplex.Cochain.tensor f convOne).v r s hrs` is determined by the
surviving `i₂ = 0` summand: it vanishes when `i₂ ≠ 0` by
`tensor_f_convOne_support_collapse`, and at `(r, 0)` it equals the explicit
signed summand (whose sign is `(0 * r).negOnePow`). This packages the descent
half of the right-unit reduction; the one-sided composition interchange, the
`comul_counit` / `mul_one` slides, and the final right-unitor-around-`f`
identification are consumed by `conv_one_right` below. No
`IsComonHom`/`IsMonHom` hypothesis is introduced. -/
private theorem tensor_f_convOne_desc_singleton {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s) :
    (HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) r 0 r (add_zero r) ≫
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A))).v
        r s hrs =
      (0 * r).negOnePow •
        (f.v r (r + n) rfl ⊗ₘ
          (convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl) ≫
        HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₂ : i₂ ≠ 0),
      HomologicalComplex.ιMapBifunctor C C (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A))).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₂ => tensor_f_convOne_support_collapse f r s hrs i₁ i₂ hij hi₂⟩

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] [MonObj A] [ComonObj C] in
/-- Degree-cast computation for cochains: transporting a cochain along a degree
equality computes at components by reusing the original component with the
transported degree proof.

Searched pinned `HomComplex.lean` (`Cochain`, `Triplet`, `mk`, `v`, `congr_v`,
`ext`, `comp`, `ofHom`, `XIsoOfEq`), `HomComplexShift.lean` (`rightShift`,
`leftShift`, `rightUnshift`, `leftUnshift`, `shift`), nearby
`TwistingCochain.lean` (`conv`, `tensorCochain`, `convSummand`) and
`TensorCochainCoherence.lean` (`tensor`, `tensor_v`,
`ofHom_tensorHom_comp_tensor`, `tensor_comp_ofHom_tensorHom`, `tensor_assoc`):
no pinned cochain degree-cast computation exists, so this smallest reusable
bridge is added locally. -/
private theorem cochain_cast_v {a b : ℤ} (hab : a = b)
    (z : HomComplex.Cochain C A a) (r s : ℤ) (hrs : r + b = s) :
    (cast (congrArg (HomComplex.Cochain C A) hab) z).v r s hrs =
      z.v r s (by omega) := by
  subst hab
  rfl

/-- Right-unit transport ingredients for the surviving degree-zero summand.

For `f : HomComplex.Cochain C A n`, the five components below are the
verified cochain-level pieces that turn the surviving `i₂ = 0` summand of
`conv f convOne` into `f`:
* the `congr_v` component forms of the two right-unit slides (comultiplication/
  counit side via pinned `ComonObj.comul_counit`, unit/multiplication side via
  pinned `MonObj.mul_one`);
* the one-sided interchange `ofHom_tensorHom_comp_tensor` at unit degrees
  `(𝟙 C, 𝟙 C, f, convOne)`, pinning the exact rewrite shape consumed by the
  `tensor f convOne` factorization;
* the graded right-unitor expansion `HomologicalComplex.rightUnitor'_inv` at
  `C`, identifying the surviving summand's
  `(ρ_ _).inv ≫ ... ≫ ιTensorObj` pattern with `(rightUnitor' C).inv`;
* the degree-cast computation `cochain_cast_v` at `add_zero n`, moving the
  `cast (congrArg _ (add_zero n))` past `.v` (`n + 0` is not definitionally
  `n`, so the cast proof is supplied by `omega` explicitly).

Exact typed equality closed by `conv_one_right` below:
`cast (congrArg (HomComplex.Cochain C A) (add_zero n)) (conv f convOne) = f`
for `f : HomComplex.Cochain C A n`. It factors `tensor f convOne` through the
one-sided middle interchange (`tensor_f_convOne_middle_interchange`),
collapses the inner `tensor f (ofHom one)` to its `i₂ = 0` summand
(`tensor_desc_singleton_one` with explicit `(0 * r).negOnePow` clearance),
and closes the surviving `ModuleCat` composite with the `TensorUnitor`
generator formulas plus right-unitor naturality. No `IsComonHom`/`IsMonHom`
hypothesis is introduced. -/
private theorem conv_one_right_transport {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s) :
    ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.counit (X := C)))
      (zero_add 0))).v r r (add_zero r) =
      (HomComplex.Cochain.ofHom (ρ_ C).inv).v r r (add_zero r)) ∧
    ((((HomComplex.Cochain.ofHom (A ◁ MonObj.one (X := A)))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (zero_add 0))).v s s (add_zero s) =
      (HomComplex.Cochain.ofHom (ρ_ A).hom).v s s (add_zero s) ∧
    ((HomComplex.Cochain.ofHom
      (HomologicalComplex.tensorHom (𝟙 C) (𝟙 C))).comp
      (HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A)))
      (zero_add (n + 0))) =
      HomComplex.Cochain.tensor
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n))
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp
          (convOne (R := R) (C := C) (A := A)) (zero_add 0)) ∧
    ((HomologicalComplex.rightUnitor' C).inv r =
      (ρ_ (C.X r)).inv ≫
        (((C.X r) ◁ ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv))) ≫
        HomologicalComplex.ιTensorObj C
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
          r 0 r (add_zero r)) ∧
    ((cast (congrArg (HomComplex.Cochain C A) (add_zero n))
      (conv f (convOne (R := R) (C := C) (A := A)))).v r s (by omega : r + n = s) =
      (conv f (convOne (R := R) (C := C) (A := A))).v r s hrs) := by
  have hC : ComonObj.comul (X := C) ≫ C ◁ ComonObj.counit (X := C) = (ρ_ C).inv :=
    ComonObj.comul_counit C
  have hCOf := congrArg HomComplex.Cochain.ofHom hC
  rw [HomComplex.Cochain.ofHom_comp] at hCOf
  have hA : A ◁ MonObj.one (X := A) ≫ MonObj.mul (X := A) = (ρ_ A).hom :=
    MonObj.mul_one A
  have hAOf := congrArg HomComplex.Cochain.ofHom hA
  rw [HomComplex.Cochain.ofHom_comp] at hAOf
  exact ⟨HomComplex.Cochain.congr_v hCOf r r (add_zero r),
    HomComplex.Cochain.congr_v hAOf s s (add_zero s),
    HomComplex.Cochain.ofHom_tensorHom_comp_tensor (𝟙 C) (𝟙 C) f
      (convOne (R := R) (C := C) (A := A)),
    HomologicalComplex.rightUnitor'_inv C r,
    cochain_cast_v (add_zero n) (conv f (convOne (R := R) (C := C) (A := A)))
      r s (by omega : r + n = s)⟩

/-- `conv` at components via heterogeneous `Cochain.tensor`, for reuse by the
associativity proof (triple-sum `hmid` with transports). -/
private theorem conv_tensor_v {m n : ℤ} (f : HomComplex.Cochain C A m)
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (m + n) = s) :
    (conv f g).v r s hrs =
      (ComonObj.comul (X := C)).f r ≫
        (HomComplex.Cochain.tensor f g).v r s (by omega) ≫
          (MonObj.mul (X := A)).f s := by
  rw [conv_eq f g,
    HomComplex.Cochain.comp_v _ _ _ r s s (by omega) (add_zero s),
    HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega),
    HomComplex.Cochain.ofHom_v, HomComplex.Cochain.ofHom_v,
    Category.assoc]

/-- Degree transport for nested convolution: the outer `v`-degree of
`conv (conv f g) h` rewrites to that of `conv f (conv g h)`.
The `hmid` step assembles `tensorCochain_assoc`,
`HomComplex.Cochain.tensor_assoc`, `ComonObj.comul_assoc`, and
`MonObj.mul_assoc` through heterogeneous triple descs on top of this
transport. -/
private theorem conv_assoc_v_degree {m n p r s : ℤ}
    (hrs : r + ((m + n) + p) = s) : r + (m + (n + p)) = s := by
  omega

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Negation pushes through the left factor of `⊗ₘ`, from additivity. -/
private lemma neg_tensorHom_left {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((-f) ⊗ₘ g) = -((f ⊗ₘ g)) := by
  have h : ((-f) ⊗ₘ g) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.add_tensor, neg_add_cancel,
      MonoidalPreadditive.zero_tensor]
  exact eq_neg_of_add_eq_zero_left h

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Negation pushes through the right factor of `⊗ₘ`, from additivity. -/
private lemma neg_tensorHom_right {X₁ Y₁ X₂ Y₂ : ModuleCat R}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (-g))) = -((f ⊗ₘ g)) := by
  have h : ((f ⊗ₘ (-g))) + ((f ⊗ₘ g)) = 0 := by
    rw [← MonoidalPreadditive.tensor_add, neg_add_cancel,
      MonoidalPreadditive.tensor_zero]
  exact eq_neg_of_add_eq_zero_left h

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- A unit scalar pushes through the left factor of `⊗ₘ`. -/
private lemma tensorHom_units_smul_left {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((k • f) ⊗ₘ g) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_left]

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- A unit scalar pushes through the right factor of `⊗ₘ`. -/
private lemma tensorHom_units_smul_right {X₁ Y₁ X₂ Y₂ : ModuleCat R} (k : ℤˣ)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : ((f ⊗ₘ (k • g))) = k • (f ⊗ₘ g) := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
  · simp only [Units.neg_smul, one_smul, neg_tensorHom_right]

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Heterogeneous tensor-of-composites interchange with the Koszul sign
`(n₂ * m₁).negOnePow`.

For `a₁ : Cochain C₁ A₁ m₁`, `b₁ : Cochain A₁ B₁ n₁`,
`a₂ : Cochain C₂ A₂ m₂`, `b₂ : Cochain A₂ B₂ n₂`, composing the tensor
products equals the signed tensor product of the composites: the left side
carries the separate signs `(m₂ * i₁)` and `(n₂ * (i₁ + m₁))`, whose total is
the right side outer sign `((m₂ + n₂) * i₁)` plus the interchange excess
`(n₂ * m₁)`. Proved by descending with pinned `tensor_v`, `comp_v`,
`mapBifunctor` descent/inclusion, `tensorHom_comp_tensorHom`, and the
tensor-hom smul bridges above.

Consumed by the triple-sum `hmid` step of `conv_assoc` below:
`((conv f g).tensor h).v = (f.tensor (conv g h)).v` with transports, via
`tensorCochain_assoc`, `HomComplex.Cochain.tensor_assoc`,
`ComonObj.comul_assoc`, and `MonObj.mul_assoc` through heterogeneous triple
descs (`mapBifunctor₁₂.hom_ext`, `ι_eq`, associator naturality). -/
private theorem tensor_comp_tensor {C₁ C₂ A₁ A₂ B₁ B₂ : CochainComplex (ModuleCat R) ℤ}
    {m₁ n₁ m₂ n₂ : ℤ}
    (a₁ : HomComplex.Cochain C₁ A₁ m₁) (b₁ : HomComplex.Cochain A₁ B₁ n₁)
    (a₂ : HomComplex.Cochain C₂ A₂ m₂) (b₂ : HomComplex.Cochain A₂ B₂ n₂)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X]
    [GradedObject.HasTensor B₁.X B₂.X] :
    (HomComplex.Cochain.tensor a₁ a₂).comp (HomComplex.Cochain.tensor b₁ b₂)
      (by omega : (m₁ + m₂) + (n₁ + n₂) = (m₁ + n₁) + (m₂ + n₂)) =
      (n₂ * m₁).negOnePow •
        HomComplex.Cochain.tensor (a₁.comp b₁ rfl) (a₂.comp b₂ rfl) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [HomComplex.Cochain.comp_v _ _ _ r (r + (m₁ + m₂)) s (by omega) (by omega),
    HomComplex.Cochain.tensor_v, HomComplex.Cochain.tensor_v,
    HomComplex.Cochain.units_smul_v, HomComplex.Cochain.tensor_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  have hij : i₁ + i₂ = r := hh
  have hsign : m₂ * i₁ + n₂ * (i₁ + m₁) = (m₂ + n₂) * i₁ + n₂ * m₁ := by
    rw [mul_add, add_mul]
    ac_rfl
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  rw [Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  conv_rhs => rw [Linear.comp_units_smul, HomologicalComplex.ι_mapBifunctorDesc]
  rw [HomComplex.Cochain.comp_v a₁ b₁ rfl i₁ (i₁ + m₁) _ rfl (by omega),
    HomComplex.Cochain.comp_v a₂ b₂ rfl i₂ (i₂ + m₂) _ rfl (by omega)]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add]
  rw [hsign, add_comm (n₂ * m₁) ((m₂ + n₂) * i₁), Category.assoc]
  have key : ∀ (y1 y2 : ℤ) (hy1 : (i₁ + m₁) + n₁ = y1) (hy2 : (i₂ + m₂) + n₂ = y2)
      (hι : y1 + y2 = s),
      (b₁.v (i₁ + m₁) y1 hy1 ⊗ₘ b₂.v (i₂ + m₂) y2 hy2) ≫
        HomologicalComplex.ιTensorObj B₁ B₂ y1 y2 s hι =
      (b₁.v (i₁ + m₁) ((i₁ + m₁) + n₁) rfl ⊗ₘ
        b₂.v (i₂ + m₂) ((i₂ + m₂) + n₂) rfl) ≫
        HomologicalComplex.ιTensorObj B₁ B₂ ((i₁ + m₁) + n₁) ((i₂ + m₂) + n₂) s
          (by omega) := by
    intro y1 y2 hy1 hy2 hι
    subst hy1
    subst hy2
    rfl
  rw [key _ _ (add_assoc i₁ m₁ n₁) (add_assoc i₂ m₂ n₂) (by omega)]

omit [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensor₁₂Tensor X₂ X₃] [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  X₁.HasGoodTensorTensor₂₃ X₂ X₃] in
/-- Triple interchange through heterogeneous tensors, by double `tensor_comp_tensor`.

For three layers of tensor products, composing vertically equals the signed
tensor product of the triple composites, with combined Koszul sign
`(n₂ * m₁ + p₂ * (m₁ + n₁)).negOnePow`. Proved by rewriting the inner
interchange with `tensor_comp_tensor`, pushing the unit scalar through
composition (`units_smul_comp`), rewriting the outer interchange, then
combining signs (`smul_smul`, `Int.negOnePow_add`).

Reusable in the convolution associativity proof: after unfolding outer
`conv` via `conv_tensor_v`, the middle `tensor (conv f g) h` is factored
into triple-tensor comps before `tensorCochain_assoc`, `Cochain.tensor_assoc`,
`ComonObj.comul_assoc`, `MonObj.mul_assoc`, associator naturality, and triple
`mapBifunctor₁₂.hom_ext`/`ι_eq` close the `hmid` triple sum consumed by
`conv_assoc` below.

Heterogeneous factorization note: `tensor (conv f g) h` has outer `ofHom`
(comul/mul, degree `0`) factors rather than tensors, so this triple-tensor
interchange does not directly apply there; `Cochain.tensor_assoc`
reassociation of `(tensor f g).tensor h` vs `tensor f (tensor g h)` through
complex associators, plus `comul_assoc`/`mul_assoc` slides and triple-desc
peeling, complete that step in `conv_assoc`. -/
private theorem tensor_comp_tensor_three {C₁ C₂ A₁ A₂ B₁ B₂ D₁ D₂ : CochainComplex (ModuleCat R) ℤ}
    {m₁ n₁ p₁ m₂ n₂ p₂ : ℤ}
    (a₁ : HomComplex.Cochain C₁ A₁ m₁) (b₁ : HomComplex.Cochain A₁ B₁ n₁)
    (c₁ : HomComplex.Cochain B₁ D₁ p₁)
    (a₂ : HomComplex.Cochain C₂ A₂ m₂) (b₂ : HomComplex.Cochain A₂ B₂ n₂)
    (c₂ : HomComplex.Cochain B₂ D₂ p₂)
    [GradedObject.HasTensor C₁.X C₂.X] [GradedObject.HasTensor A₁.X A₂.X]
    [GradedObject.HasTensor B₁.X B₂.X] [GradedObject.HasTensor D₁.X D₂.X] :
    (((HomComplex.Cochain.tensor a₁ a₂).comp (HomComplex.Cochain.tensor b₁ b₂)
      (by omega : (m₁ + m₂) + (n₁ + n₂) = (m₁ + n₁) + (m₂ + n₂))).comp
      (HomComplex.Cochain.tensor c₁ c₂)
      (by omega : ((m₁ + n₁) + (m₂ + n₂)) + (p₁ + p₂) =
        ((m₁ + n₁) + p₁) + ((m₂ + n₂) + p₂))) =
      (n₂ * m₁ + p₂ * (m₁ + n₁)).negOnePow •
        HomComplex.Cochain.tensor ((a₁.comp b₁ rfl).comp c₁ rfl)
          ((a₂.comp b₂ rfl).comp c₂ rfl) := by
  have h1 := tensor_comp_tensor a₁ b₁ a₂ b₂
  rw [h1, HomComplex.Cochain.units_smul_comp]
  have h2 := tensor_comp_tensor (a₁.comp b₁ rfl) c₁ (a₂.comp b₂ rfl) c₂
  rw [h2, smul_smul, ← Int.negOnePow_add]

/-- Heterogeneous left factorization of `tensor (conv f g) h`.

The tensor of a convolution with a cochain factors through the triple tensor
`tensor (tensor f g) h`, with degree-`0` `ofHom` outer factors
`tensorHom comul 𝟙` and `tensorHom mul 𝟙`. Proved from `conv_eq` and the
pinned pre/postcomposition factorizations
`ofHom_tensorHom_comp_tensor` / `tensor_comp_ofHom_tensorHom`, closing the
identity sides by `Cochain.id_comp` / `Cochain.comp_id`. Signs are trivial
because the outer factors have degree `0`; the pure triple-tensor
interchange (`tensor_comp_tensor_three`) is consumed by the subsequent
`hmid` triple sum of `conv_assoc` below, together with the
`Cochain.tensor_assoc` reassociation and the `comul_assoc` / `mul_assoc`
slides. -/
private theorem tensor_conv_factor_left {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    HomComplex.Cochain.tensor (conv f g) h =
      (((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (ComonObj.comul (X := C)) (𝟙 C))).comp
        (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h)
        (zero_add ((m + n) + p))).comp
        (HomComplex.Cochain.ofHom
          (HomologicalComplex.tensorHom (MonObj.mul (X := A)) (𝟙 A)))
        (add_zero ((m + n) + p))) := by
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (ComonObj.comul (X := C)) (𝟙 C)
    (HomComplex.Cochain.tensor f g) h
  rw [HomComplex.Cochain.id_comp] at e_pre
  have e_post := HomComplex.Cochain.tensor_comp_ofHom_tensorHom
    ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))) h
    (MonObj.mul (X := A)) (𝟙 A)
  rw [HomComplex.Cochain.comp_id] at e_post
  have e_conv := (conv_eq f g).symm
  rw [e_pre, e_post, e_conv]

/-- Heterogeneous right factorization of `tensor f (conv g h)`.

Symmetric to `tensor_conv_factor_left`, with degree-`0` `ofHom` outer factors
`tensorHom 𝟙 comul` and `tensorHom 𝟙 mul` around the triple tensor
`tensor f (tensor g h)`. Same proof shape; `Cochain.tensor_assoc` and the
`comul_assoc` / `mul_assoc` slides are consumed in the `hmid` step of
`conv_assoc` below. -/
private theorem tensor_conv_factor_right {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    HomComplex.Cochain.tensor f (conv g h) =
      (((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (𝟙 C) (ComonObj.comul (X := C)))).comp
        (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
        (zero_add (m + (n + p)))).comp
        (HomComplex.Cochain.ofHom
          (HomologicalComplex.tensorHom (𝟙 A) (MonObj.mul (X := A))))
        (add_zero (m + (n + p)))) := by
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (𝟙 C) (ComonObj.comul (X := C))
    f (HomComplex.Cochain.tensor g h)
  rw [HomComplex.Cochain.id_comp] at e_pre
  have e_post := HomComplex.Cochain.tensor_comp_ofHom_tensorHom
    f ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.tensor g h) (zero_add (n + p)))
    (𝟙 A) (MonObj.mul (X := A))
  rw [HomComplex.Cochain.comp_id] at e_post
  have e_conv := (conv_eq g h).symm
  rw [e_pre, e_post, e_conv]

/-- Cochain-level comultiplication slide for convolution associativity.

Lifting `ComonObj.comul_assoc` through `Cochain.ofHom`: the right-associated
outer comultiplication equals the left-associated outer comultiplication
followed by the complex associator. All factors have degree `0`, so transports
are `zero_add`. Proved from `ofHom_comp` and `comul_assoc`; the heterogeneous
triple-descent combining this slide with `Cochain.tensor_assoc` is consumed
by `conv_assoc` below. -/
private theorem ofHom_comul_slide :
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.comul (X := C))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C) ▷ C)).comp
        (HomComplex.Cochain.ofHom (α_ C C C).hom) (zero_add 0))
      (zero_add 0) := by
  have hC : ComonObj.comul (X := C) ≫ C ◁ ComonObj.comul (X := C) =
      ComonObj.comul (X := C) ≫ (ComonObj.comul (X := C) ▷ C) ≫ (α_ C C C).hom :=
    ComonObj.comul_assoc C
  have hOf := congrArg HomComplex.Cochain.ofHom hC
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

/-- Cochain-level multiplication slide for convolution associativity.

Lifting `MonObj.mul_assoc` through `Cochain.ofHom`: the left-associated outer
multiplication equals the complex associator followed by the right-associated
outer multiplication. All factors have degree `0`. Proved from `ofHom_comp`
and `mul_assoc`; the heterogeneous triple-descent combining this slide with
`Cochain.tensor_assoc` is consumed by `conv_assoc` below. -/
private theorem ofHom_mul_slide :
    (HomComplex.Cochain.ofHom (MonObj.mul (X := A) ▷ A)).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (α_ A A A).hom).comp
      ((HomComplex.Cochain.ofHom (A ◁ MonObj.mul (X := A))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0))
      (zero_add 0) := by
  have hA : (MonObj.mul (X := A) ▷ A) ≫ MonObj.mul (X := A) =
      (α_ A A A).hom ≫ (A ◁ MonObj.mul (X := A)) ≫ MonObj.mul (X := A) :=
    MonObj.mul_assoc A
  have hOf := congrArg HomComplex.Cochain.ofHom hA
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

/-- Cochain-level counit slide for the convolution left unit.

Lifting `ComonObj.counit_comul` through `Cochain.ofHom`: comultiplication
followed by the counit whiskering equals the complex left unitor inverse.
All factors have degree `0`. Proved from `ofHom_comp` and `counit_comul`;
consumed by `conv_one_left` and `conv_one_right` below together with the
heterogeneous support-collapse (`convOne_vanish`), one-sided interchange,
and unitor transport lifting `leftUnitor'_inv`. -/
private theorem ofHom_counit_slide :
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C) ▷ C)) (zero_add 0) =
    HomComplex.Cochain.ofHom (λ_ C).inv := by
  have hC : ComonObj.comul (X := C) ≫ ComonObj.counit (X := C) ▷ C = (λ_ C).inv :=
    ComonObj.counit_comul C
  have hOf := congrArg HomComplex.Cochain.ofHom hC
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

/-- Cochain-level unit slide for the convolution left unit.

Lifting `MonObj.one_mul` through `Cochain.ofHom`: the unit whiskering
followed by multiplication equals the complex left unitor. All factors have
degree `0`. Proved from `ofHom_comp` and `one_mul`; consumed by
`conv_one_left` below via `conv_eq`, `convOne`, `counit_comul_hom` /
`one_mul_hom`, and the cochain-level unitor transport lifting
`leftUnitor'_inv` with degree cast `cochain_cast_v`. -/
private theorem ofHom_one_slide :
    (HomComplex.Cochain.ofHom (MonObj.one (X := A) ▷ A)).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0) =
    HomComplex.Cochain.ofHom (λ_ A).hom := by
  have hA : MonObj.one (X := A) ▷ A ≫ MonObj.mul (X := A) = (λ_ A).hom :=
    MonObj.one_mul A
  have hOf := congrArg HomComplex.Cochain.ofHom hA
  rw [HomComplex.Cochain.ofHom_comp] at hOf
  exact hOf

omit [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).obj X)] [∀ (X : ModuleCat R),
  PreservesColimit (Functor.empty.{0} (ModuleCat R))
    ((curriedTensor (ModuleCat R)).flip.obj X)] [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  X₁.HasTensor₄ObjExt X₂ X₃ X₄] [MonObj A] [ComonObj C] in
/-- Triple-tensor reassociation for the convolution `hmid` step.

This is `HomComplex.Cochain.tensor_assoc` specialized to the convolution
triple (`C₁=C₂=C₃=C`, `A₁=A₂=A₃=A`). It relates the two triple tensors
appearing after `tensor_conv_factor_left`/`tensor_conv_factor_right` through
the complex associators; its `.v` form (via `Cochain.congr_v`) is the middle
piece of the `hmid` triple sum consumed by `conv_assoc` below, together with
the triple-descent peeling this reassociation with the outer
`ofHom_comul_slide`/`ofHom_mul_slide` through heterogeneous triple descs
(`mapBifunctor₁₂.hom_ext`, `ι_eq`) and associator naturality. -/
private theorem tensor_assoc_hmid {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h).comp
      (HomComplex.Cochain.ofHom
        (HomologicalComplex.associator A A A).hom) (add_zero (m + n + p)) =
    (HomComplex.Cochain.ofHom
        (HomologicalComplex.associator C C C).hom).comp
      (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
      (by omega) := by
  exact HomComplex.Cochain.tensor_assoc f g h

/-- Heterogeneous triple-descent middle equality for convolution associativity.

The left-associated five-fold composite (outer `comul`/`comul ▷ C`, triple
tensor `(tensor f g).tensor h`, outer `mul ▷ A`/`mul`) agrees at components
with the right-associated five-fold composite (outer `comul`/`C ◁ comul`,
triple tensor `tensor f (tensor g h)`, outer `A ◁ mul`/`mul`), up to the
graded degree transport `conv_assoc_v_degree`.

Proved by descending the outer degree-`0` composites with pinned `comp_v` /
`zero_cochain_comp_v` / `comp_zero_cochain_v` / `ofHom_v`, peeling the middle
triple tensor with `HomologicalComplex.mapBifunctor₁₂.hom_ext`,
`HomologicalComplex.mapBifunctor₁₂.ι_eq`,
`HomologicalComplex.mapBifunctor₂₃.ι_eq`, and closing the triple summands with
`ofHom_comul_slide` / `ofHom_mul_slide` at `.f` level, `tensor_assoc_hmid`
at triple-summand level, `MonoidalCategory.associator_naturality`, and the
Koszul sign identity as in `tensor_assoc_sign`. No surrogate axiom, stronger
hypothesis, or alternate convolution definition.

Consumed by public graded `conv_assoc` below: the outer `conv` degrees
`(m + n) + p` vs `m + (n + p)` differ by `add_assoc`; the `.v` transport is
`conv_assoc_v_degree` and the cochain-level degree cast is `cochain_cast_v`. -/
private theorem conv_assoc_hmid_middle_v {m n p r s : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p)
    (hrs : r + ((m + n) + p) = s) :
    (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (ComonObj.comul (X := C) ▷ C)) (zero_add 0)).comp
      (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h)
      (zero_add ((m + n) + p))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A) ▷ A))
      (add_zero ((m + n) + p))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (add_zero ((m + n) + p))).v r s hrs =
    (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.comul (X := C))) (zero_add 0)).comp
      (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
      (zero_add (m + (n + p)))).comp
      (HomComplex.Cochain.ofHom (A ◁ MonObj.mul (X := A)))
      (add_zero (m + (n + p)))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (add_zero (m + (n + p)))).v r s (conv_assoc_v_degree hrs) := by
  have hC : (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (C ◁ ComonObj.comul (X := C))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C) ▷ C)).comp
        (HomComplex.Cochain.ofHom (α_ C C C).hom) (zero_add 0))
      (zero_add 0) := ofHom_comul_slide
  have hC_v := HomComplex.Cochain.congr_v hC r r (add_zero r)
  have hA : (HomComplex.Cochain.ofHom (MonObj.mul (X := A) ▷ A)).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0) =
    (HomComplex.Cochain.ofHom (α_ A A A).hom).comp
      ((HomComplex.Cochain.ofHom (A ◁ MonObj.mul (X := A))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (zero_add 0))
      (zero_add 0) := ofHom_mul_slide
  have hA_v := HomComplex.Cochain.congr_v hA s s (add_zero s)
  have hM := tensor_assoc_hmid f g h
  have hM_v := HomComplex.Cochain.congr_v hM r s hrs
  have hαC : (α_ C C C).hom = (HomologicalComplex.associator C C C).hom := rfl
  have hαA : (α_ A A A).hom = (HomologicalComplex.associator A A A).hom := rfl
  simp only [HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v] at hC_v hA_v hM_v ⊢
  rw [hC_v]
  simp only [Category.assoc] at ⊢
  rw [hA_v]
  rw [hαC, hαA] at ⊢
  conv_lhs =>
    arg 2
    arg 2
    rw [← Category.assoc]
    rw [hM_v]
    rw [HomComplex.Cochain.comp_v _ _ _ r r s (add_zero r) (by omega)]
    simp only [HomComplex.Cochain.ofHom_v]
    rw [Category.assoc]

/-- Graded convolution associativity, up to the `add_assoc` degree transport.

The transport uses only stdlib `cast`/`congrArg`; its computation is the local
`cochain_cast_v` bridge above. After `Cochain.ext`, both sides unfold via
`conv_tensor_v` and the `congr_v` forms of `tensor_conv_factor_left`/
`tensor_conv_factor_right` to the five-fold composites of
`conv_assoc_hmid_middle_v`, which closes the components (outer `tensorHom`
factors are definitionally the `▷`/`◁` whiskerings by the pinned monoidal
structure). No new convolution definition and no stronger hypotheses. -/
theorem conv_assoc {m n p : ℤ}
    (f : HomComplex.Cochain C A m) (g : HomComplex.Cochain C A n)
    (h : HomComplex.Cochain C A p) :
    cast (congrArg (HomComplex.Cochain C A) (add_assoc m n p))
        (conv (conv f g) h) =
      conv f (conv g h) := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [cochain_cast_v (add_assoc m n p)]
  have eL : conv (conv f g) h =
      (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (ComonObj.comul (X := C)) (𝟙 C))) (zero_add 0)).comp
        (HomComplex.Cochain.tensor (HomComplex.Cochain.tensor f g) h)
        (zero_add ((m + n) + p))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (MonObj.mul (X := A)) (𝟙 A)))
        (add_zero ((m + n) + p))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (add_zero ((m + n) + p))) := by
    rw [conv_eq (conv f g) h, tensor_conv_factor_left f g h]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show (m + n) + p + 0 = (m + n) + p from add_zero _)]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show 0 + ((m + n) + p) = (m + n) + p from zero_add _)]
  have eR : conv f (conv g h) =
      (((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (𝟙 C) (ComonObj.comul (X := C)))) (zero_add 0)).comp
        (HomComplex.Cochain.tensor f (HomComplex.Cochain.tensor g h))
        (zero_add (m + (n + p)))).comp
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (𝟙 A) (MonObj.mul (X := A))))
        (add_zero (m + (n + p)))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
        (add_zero (m + (n + p)))) := by
    rw [conv_eq f (conv g h), tensor_conv_factor_right f g h]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show m + (n + p) + 0 = m + (n + p) from add_zero _)]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
      (show 0 + (m + (n + p)) = m + (n + p) from zero_add _)]
  rw [eL, eR]
  exact conv_assoc_hmid_middle_v f g h (by omega : r + ((m + n) + p) = s)

/-- Left-unit transport ingredients for the surviving degree-zero summand.

For `f : HomComplex.Cochain C A n`, the five components below are the
verified cochain-level pieces that turn the surviving `i₁ = 0` summand of
`conv convOne f` into `f`:
* the `congr_v` component forms of the two unit slides `ofHom_counit_slide`
  (comultiplication/counit side) and `ofHom_one_slide`
  (unit/multiplication side);
* the one-sided interchange `ofHom_tensorHom_comp_tensor` at unit degrees
  `(𝟙 C, 𝟙 C, convOne, f)`, pinning the exact rewrite shape consumed by the
  `tensor convOne f` factorization;
* the graded left-unitor expansion `HomologicalComplex.leftUnitor'_inv` at
  `C`, identifying the surviving summand's
  `(λ_ _).inv ≫ ... ≫ ιTensorObj` pattern with `(leftUnitor' C).inv`;
* the degree-cast computation `cochain_cast_v` at `zero_add n`, moving the
  `cast (congrArg _ (zero_add n))` past `.v`.

Exact typed equality closed by `conv_one_left` below:
`cast (congrArg (HomComplex.Cochain C A) (zero_add n)) (conv convOne f) = f`.
It factors `tensor convOne f` through the one-sided middle interchange
(`tensor_convOne_middle_interchange`), collapses the inner
`tensor (ofHom one) f` to its `i₁ = 0` summand (`tensor_one_desc_singleton`),
and closes the surviving `ModuleCat` composite with the `TensorUnitor`
generator formulas plus unitor naturality. No `IsComonHom`/`IsMonHom`
hypothesis is introduced. -/
private theorem conv_one_left_transport {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    ((((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C) ▷ C))
      (zero_add 0))).v r r (add_zero r) =
      (HomComplex.Cochain.ofHom (λ_ C).inv).v r r (add_zero r)) ∧
    ((((HomComplex.Cochain.ofHom (MonObj.one (X := A) ▷ A))).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A)))
      (zero_add 0))).v s s (add_zero s) =
      (HomComplex.Cochain.ofHom (λ_ A).hom).v s s (add_zero s) ∧
    ((HomComplex.Cochain.ofHom
      (HomologicalComplex.tensorHom (𝟙 C) (𝟙 C))).comp
      (HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f)
      (zero_add (0 + n))) =
      HomComplex.Cochain.tensor
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp
          (convOne (R := R) (C := C) (A := A)) (zero_add 0))
        ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) ∧
    ((HomologicalComplex.leftUnitor' C).inv r =
      (λ_ (C.X r)).inv ≫
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv) ▷ (C.X r)) ≫
        HomologicalComplex.ιTensorObj
          (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)) C
          0 r r (zero_add r)) ∧
    ((cast (congrArg (HomComplex.Cochain C A) (zero_add n))
      (conv (convOne (R := R) (C := C) (A := A)) f)).v r s (by omega : r + n = s) =
      (conv (convOne (R := R) (C := C) (A := A)) f).v r s hrs) := by
  exact ⟨HomComplex.Cochain.congr_v ofHom_counit_slide r r (add_zero r),
    HomComplex.Cochain.congr_v ofHom_one_slide s s (add_zero s),
    HomComplex.Cochain.ofHom_tensorHom_comp_tensor (𝟙 C) (𝟙 C)
      (convOne (R := R) (C := C) (A := A)) f,
    HomologicalComplex.leftUnitor'_inv C r,
    cochain_cast_v (zero_add n) (conv (convOne (R := R) (C := C) (A := A)) f)
      r s (by omega : r + n = s)⟩

/-- Unitor-assembly sign clearance for the surviving `i₁ = 0` summand.

For `f : HomComplex.Cochain C A n`, the surviving component isolated by
`tensor_convOne_desc_singleton` carries the Koszul sign `(n * 0).negOnePow`,
which is `1`. Clearing it exposes the unsigned composite that the final
unitor-around-`f` identification consumed through the existing one-sided
interchange (`ofHom_tensorHom_comp_tensor` at unit degrees, as pinned in
`conv_one_left_transport`), the slides `ofHom_counit_slide`/`ofHom_one_slide`,
the graded expansion `HomologicalComplex.leftUnitor'_inv`, and the cast
computation `cochain_cast_v`. Consumed by `conv_one_left` below; no
`IsComonHom`/`IsMonHom` hypothesis is introduced. -/
private theorem tensor_convOne_surviving_sign {n : ℤ}
    (f : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    (n * 0).negOnePow •
      ((convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl ⊗ₘ
        f.v r (r + n) rfl) ≫
      HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega) =
    ((convOne (R := R) (C := C) (A := A)).v 0 (0 + 0) rfl ⊗ₘ
      f.v r (r + n) rfl) ≫
    HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega) := by
  simp

/-- `ofHom one` vanishes in nonzero degree: it factors through the tensor-unit
graded object, which is zero away from `0` (`isZero_single_obj_X`), via the
source-zero side. Inner-collapse counterpart of `convOne_vanish` for the
middle-interchange survivor `tensor (ofHom one) f`. -/
private theorem one_vanish (i : ℤ) (hi : i ≠ 0) :
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i i (by omega) = 0 := by
  rw [HomComplex.Cochain.ofHom_v]
  have h0 : IsZero
      ((HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).X i) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat R)) i hi
  exact h0.eq_of_src _ _

/-- General support-collapse form of `one_vanish` for arbitrary target degree,
mirroring `convOne_vanish_general`. -/
private theorem one_vanish_general (i j : ℤ) (hij : i + (0 : ℤ) = j)
    (hi : i ≠ 0) :
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i j hij = 0 := by
  have hj : i = j := by omega
  subst hj
  exact one_vanish i hi

omit [ComonObj C] in
/-- Vanishing of non-degree-zero summands in `tensor (ofHom one) g`,
mirroring `tensor_convOne_summand_vanish` for the inner middle-interchange
tensor. -/
private theorem tensor_one_summand_vanish {n : ℤ}
    (g : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₁ : i₁ ≠ 0) :
    (n * i₁).negOnePow •
      ((HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₁ (i₁ + 0) rfl ⊗ₘ
        g.v i₂ (i₂ + n) rfl) = 0 := by
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₁ (i₁ + 0) rfl = 0 :=
    one_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

omit [ComonObj C] in
/-- Support collapse of `tensor (ofHom one) g` to its surviving `i₁ = 0`
summand, mirroring `tensor_convOne_support_collapse`. -/
private theorem tensor_one_support_collapse {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₁ : i₁ ≠ 0) :
    HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) g).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₁ (i₁ + 0) rfl = 0 :=
    one_vanish_general i₁ (i₁ + 0) rfl hi₁
  rw [h0, MonoidalPreadditive.zero_tensor]
  simp

omit [ComonObj C] in
/-- Singleton-desc identification for `tensor (ofHom one) g`, mirroring
`tensor_convOne_desc_singleton`. -/
private theorem tensor_one_desc_singleton {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (0 + n) = s) :
    (HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) 0 r r (zero_add r) ≫
      (HomComplex.Cochain.tensor
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) g).v
        r s hrs =
      (n * 0).negOnePow •
        ((HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl ⊗ₘ
          g.v r (r + n) rfl) ≫
        HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₁ : i₁ ≠ 0),
      HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) g).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₁ => tensor_one_support_collapse g r s hrs i₁ i₂ hij hi₁⟩

/-- One-sided middle interchange for `tensor convOne f` (left).

Unfolds `convOne = (ofHom counit).comp (ofHom one)` then factors the tensor
through the pinned `ofHom_tensorHom_comp_tensor` at `(counit, 𝟙)`. The Koszul
excess is `(n * 0)` hence `1` by the same `simp` as
`tensor_convOne_surviving_sign` (pinned `tensor_comp_tensor` sign with
`m₁ = 0`); identity sides close by `Cochain.id_comp`. This exposes the exact
`hC_v`/`hA_v` patterns (`ofHom_counit_slide`/`ofHom_one_slide` in `congr_v`
form) after `conv_tensor_v`. -/
private theorem tensor_convOne_middle_interchange {n : ℤ}
    (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain.tensor (convOne (R := R) (C := C) (A := A)) f =
      ((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (ComonObj.counit (X := C)) (𝟙 C))).comp
        (HomComplex.Cochain.tensor
          (HomComplex.Cochain.ofHom (MonObj.one (X := A)))
          ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)))
        (zero_add (0 + n))) := by
  have hConv : (convOne (R := R) (C := C) (A := A)) =
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C))).comp
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) (zero_add 0) := rfl
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (ComonObj.counit (X := C)) (𝟙 C)
    (HomComplex.Cochain.ofHom (MonObj.one (X := A))) f
  rw [← hConv] at e_pre
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at e_pre ⊢
  exact e_pre.symm

/-- Convolution left unit, up to the `zero_add` degree transport.

For `f : HomComplex.Cochain C A n`, casting `conv convOne f` along
`zero_add n` gives `f`, via the one-sided middle interchange
(`tensor_convOne_middle_interchange`), the inner support-collapse of
`tensor (ofHom one) f` (`tensor_one_desc_singleton`), the slides
`ofHom_counit_slide`/`ofHom_one_slide` in `congr_v` form, the graded
expansion `HomologicalComplex.leftUnitor'_inv`, and the `ModuleCat` unitor
assembly (`ιTensorObj_tensorHom`, `ιTensorObj_leftUnitor_hom`, unitor
naturality) with the cast computation `cochain_cast_v`.

No new associativity beyond the existing `conv_assoc`, no
bar-cobar/twisting adjunctions, no derived/Koszul, no operads, no KQ. -/
theorem conv_one_left {n : ℤ} (f : HomComplex.Cochain C A n) :
    cast (congrArg (HomComplex.Cochain C A) (zero_add n))
      (conv (convOne (R := R) (C := C) (A := A)) f) = f := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [cochain_cast_v (zero_add n)]
  have eConv := conv_eq (convOne (R := R) (C := C) (A := A)) f
  have hMid := tensor_convOne_middle_interchange f
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at hMid
  have hMid_v := HomComplex.Cochain.congr_v hMid r s (by omega : r + (0 + n) = s)
  have hTrans := conv_one_left_transport f r s (by omega)
  obtain ⟨hC_v, hA_v, _, hU, _⟩ := hTrans
  have hWhiskerC : (HomologicalComplex.tensorHom
      (ComonObj.counit (X := C)) (𝟙 C)).f r =
      (ComonObj.counit (X := C) ▷ C).f r := rfl
  have hWhiskerA : (HomologicalComplex.tensorHom
      (MonObj.one (X := A)) (𝟙 A)).f s =
      (MonObj.one (X := A) ▷ A).f s := rfl
  have hOneV : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) =
      (MonObj.one (X := A)).f 0 :=
    HomComplex.Cochain.ofHom_v _ _
  have hIotaOne := HomologicalComplex.ιTensorObj_tensorHom
    (MonObj.one (X := A)) (𝟙 A) 0 (r + n) s (by omega)
  have hIdA : ((𝟙 A : A ⟶ A).f (r + n)) = 𝟙 (A.X (r + n)) := rfl
  have hLamBridge : (λ_ A).hom.f s = (HomologicalComplex.leftUnitor A).hom.f s := rfl
  have hStep : (HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) A
        0 (r + n) (r + n) (by omega) ≫
        (HomologicalComplex.leftUnitor A).hom.f (r + n)) =
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ▷ A.X (r + n)) ≫ (λ_ (A.X (r + n))).hom) :=
    HomologicalComplex.ιTensorObj_leftUnitor_hom A (r + n)
  have hWhiskerS : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ▷ A.X (r + n)) =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ⊗ₘ 𝟙 (A.X (r + n))) := rfl
  have hS : ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ⊗ₘ 𝟙 (A.X (r + n))) ≫
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom ▷ A.X (r + n)) ≫ (λ_ (A.X (r + n))).hom))) =
      (λ_ (A.X (r + n))).hom := by
    rw [hWhiskerS, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      Iso.inv_hom_id]
    simp
  have hWhiskerF : ((𝟙 (𝟙_ (ModuleCat R)) ⊗ₘ f.v r (r + n) rfl)) =
      ((𝟙_ (ModuleCat R)) ◁ f.v r (r + n) rfl) := rfl
  have hIotaIdx : HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega) =
      HomologicalComplex.ιTensorObj A A 0 (r + n) s (by omega) := by
    congr 1
  have hTail : ((((MonObj.one (X := A)).f 0 ⊗ₘ (𝟙 A : A ⟶ A).f (r + n))) ≫
      (HomologicalComplex.ιTensorObj A A 0 (r + n) s (by omega) ≫
        (MonObj.mul (X := A)).f s)) =
      (HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex (ModuleCat R) ℤ)) A
        0 (r + n) s (by omega) ≫
        ((HomologicalComplex.tensorHom (MonObj.one (X := A)) (𝟙 A)).f s ≫
          (MonObj.mul (X := A)).f s)) := by
    rw [← Category.assoc, ← hIotaOne, Category.assoc]
  have hIdx : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl =
      (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) := by
    congr 1
  have hInner := tensor_one_desc_singleton f r s (by omega : r + (0 + n) = s)
  have hSignInner : (n * 0).negOnePow = (1 : ℤˣ) := by simp
  have hUnitorBridge : (λ_ C).inv.f r = (HomologicalComplex.leftUnitor' C).inv r := rfl
  have hIotaBridge : (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ)).ιTensorObj
      C 0 r r (by omega) =
      HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) 0 r r (zero_add r) := rfl
  have hCollapse : (HomologicalComplex.ιMapBifunctor (𝟙_ (CochainComplex (ModuleCat R) ℤ)) C
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) 0 r r (zero_add r) ≫
      (((HomComplex.Cochain.ofHom (MonObj.one (X := A))).tensor f).v r s
        (by omega : r + (0 + n) = s) ≫ (MonObj.mul (X := A)).f s)) =
      (((n * 0).negOnePow •
        ((HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl ⊗ₘ
          f.v r (r + n) rfl) ≫
        HomologicalComplex.ιTensorObj A A (0 + 0) (r + n) s (by omega)) ≫
        (MonObj.mul (X := A)).f s) := by
    rw [← Category.assoc, hInner.1]
  have hFactor : (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0) ⊗ₘ f.v r (r + n) rfl) =
      ((𝟙 (𝟙_ (ModuleCat R)) ⊗ₘ f.v r (r + n) rfl) ≫
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0) ⊗ₘ
          𝟙 (A.X (r + n)))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  have hSplit : ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0) ⊗ₘ 𝟙 (A.X (r + n)))) =
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).inv ⊗ₘ 𝟙 (A.X (r + n))) ≫
        ((MonObj.one (X := A)).f 0 ⊗ₘ 𝟙 (A.X (r + n)))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  rw [eConv]
  rw [HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
    (show (0 + n) + 0 = 0 + n from add_zero _)]
  simp only [HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v] at hC_v hA_v ⊢
  rw [hMid_v] at ⊢
  rw [HomComplex.Cochain.zero_cochain_comp_v] at ⊢
  rw [HomComplex.Cochain.ofHom_v] at ⊢
  rw [hWhiskerC] at ⊢
  simp only [← Category.assoc] at ⊢
  rw [hC_v] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hUnitorBridge] at ⊢
  rw [hU] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hIotaBridge] at ⊢
  rw [hCollapse] at ⊢
  rw [hSignInner, one_smul] at ⊢
  rw [hIdx, hOneV] at ⊢
  nth_rewrite 2 [← Category.assoc] at ⊢
  rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc] at ⊢
  rw [hFactor] at ⊢
  rw [hSplit] at ⊢
  simp only [Category.assoc] at ⊢
  rw [← hIdA] at ⊢
  rw [hIotaIdx] at ⊢
  rw [hTail, hWhiskerA] at ⊢
  rw [hA_v] at ⊢
  rw [hIdA] at ⊢
  subst hrs
  rw [hLamBridge] at ⊢
  rw [hStep] at ⊢
  rw [hS] at ⊢
  rw [hWhiskerF] at ⊢
  rw [MonoidalCategory.leftUnitor_naturality] at ⊢
  simp at ⊢

omit [ComonObj C] in
/-- Vanishing of non-degree-zero summands in `tensor g (ofHom one)`,
right-mirror of `tensor_one_summand_vanish` for the inner middle-interchange
tensor. -/
private theorem tensor_summand_vanish_one {n : ℤ}
    (g : HomComplex.Cochain C A n) (i₁ i₂ : ℤ) (hi₂ : i₂ ≠ 0) :
    (0 * i₁).negOnePow •
      (g.v i₁ (i₁ + n) rfl ⊗ₘ
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₂ (i₂ + 0) rfl) = 0 := by
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₂ (i₂ + 0) rfl = 0 :=
    one_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

omit [ComonObj C] in
/-- Support collapse of `tensor g (ofHom one)` to its surviving `i₂ = 0`
summand, right-mirror of `tensor_one_support_collapse`. -/
private theorem tensor_support_collapse_one {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s)
    (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (hi₂ : i₂ ≠ 0) :
    HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor g
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v
        r s hrs = 0 := by
  rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only
  have h0 : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v i₂ (i₂ + 0) rfl = 0 :=
    one_vanish_general i₂ (i₂ + 0) rfl hi₂
  rw [h0, MonoidalPreadditive.tensor_zero]
  simp

omit [ComonObj C] in
/-- Singleton-desc identification for `tensor g (ofHom one)`, right-mirror of
`tensor_one_desc_singleton`. -/
private theorem tensor_desc_singleton_one {n : ℤ}
    (g : HomComplex.Cochain C A n) (r s : ℤ) (hrs : r + (n + 0) = s) :
    (HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) r 0 r (add_zero r) ≫
      (HomComplex.Cochain.tensor g
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v
        r s hrs =
      (0 * r).negOnePow •
        (g.v r (r + n) rfl ⊗ₘ
          (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl) ≫
        HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega)) ∧
    (∀ (i₁ i₂ : ℤ) (hij : i₁ + i₂ = r) (_hi₂ : i₂ ≠ 0),
      HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) i₁ i₂ r hij ≫
      (HomComplex.Cochain.tensor g
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v
        r s hrs = 0) := by
  exact ⟨by rw [HomComplex.Cochain.tensor_v, HomologicalComplex.ι_mapBifunctorDesc],
    fun i₁ i₂ hij hi₂ => tensor_support_collapse_one g r s hrs i₁ i₂ hij hi₂⟩

/-- One-sided middle interchange for `tensor f convOne` (right mirror).

Unfolds `convOne = (ofHom counit).comp (ofHom one)` then factors through the
pinned `ofHom_tensorHom_comp_tensor` at `(𝟙, counit)`. Koszul excess `(0 * r)`
is `1` by `simp`; identity sides by `Cochain.id_comp`/`comp_id`. Exposes the
`comul_counit`/`mul_one` slides in `congr_v` form after `conv_tensor_v`. -/
private theorem tensor_f_convOne_middle_interchange {n : ℤ}
    (f : HomComplex.Cochain C A n) :
    HomComplex.Cochain.tensor f (convOne (R := R) (C := C) (A := A)) =
      ((HomComplex.Cochain.ofHom
        (HomologicalComplex.tensorHom (𝟙 C) (ComonObj.counit (X := C)))).comp
        (HomComplex.Cochain.tensor
          ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n))
          (HomComplex.Cochain.ofHom (MonObj.one (X := A))))
        (zero_add (n + 0))) := by
  have hConv : (convOne (R := R) (C := C) (A := A)) =
      (HomComplex.Cochain.ofHom (ComonObj.counit (X := C))).comp
        (HomComplex.Cochain.ofHom (MonObj.one (X := A))) (zero_add 0) := rfl
  have e_pre := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
    (𝟙 C) (ComonObj.counit (X := C))
    f (HomComplex.Cochain.ofHom (MonObj.one (X := A)))
  rw [← hConv] at e_pre
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at e_pre ⊢
  exact e_pre.symm

/-- Convolution right unit, up to the `add_zero` degree transport.

For `f : HomComplex.Cochain C A n`, casting `conv f convOne` along
`add_zero n` gives `f`, via the one-sided middle interchange
(`tensor_f_convOne_middle_interchange`), the inner support-collapse of
`tensor f (ofHom one)` (`tensor_desc_singleton_one` with explicit
`(0 * r).negOnePow` clearance), the slides `ComonObj.comul_counit`/
`MonObj.mul_one` in `congr_v` form, the graded expansion
`HomologicalComplex.rightUnitor'_inv`, and the `ModuleCat` unitor assembly
(`ιTensorObj_tensorHom`, `ιTensorObj_rightUnitor_hom`, right-unitor
naturality) with the cast computation `cochain_cast_v`.

Order check: the survivor is `(r, 0)` (not `(0, r)`), since `i₁ + i₂ = r`
with `i₂ = 0` forces `i₁ = r`; the sign is `(0 * i₁).negOnePow` (second factor
has degree `0`). Cast check: the public transport is `add_zero n`
(`n + 0 = n`), matching `conv f convOne : Cochain C A (n + 0)`.

No new associativity beyond the existing `conv_assoc`, no
bar-cobar/twisting adjunctions, no derived/Koszul, no operads, no KQ. -/
theorem conv_one_right {n : ℤ} (f : HomComplex.Cochain C A n) :
    cast (congrArg (HomComplex.Cochain C A) (add_zero n))
      (conv f (convOne (R := R) (C := C) (A := A))) = f := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [cochain_cast_v (add_zero n)]
  have eConv := conv_eq f (convOne (R := R) (C := C) (A := A))
  have hMid := tensor_f_convOne_middle_interchange f
  have hid : ((HomComplex.Cochain.ofHom (𝟙 C)).comp f (zero_add n)) = f := by
    rw [HomComplex.Cochain.id_comp]
  rw [hid] at hMid
  have hMid_v := HomComplex.Cochain.congr_v hMid r s (by omega : r + (n + 0) = s)
  have hTrans := conv_one_right_transport f r s (by omega)
  obtain ⟨hC_v, hA_v, _, hU, _⟩ := hTrans
  have hWhiskerCR : (HomologicalComplex.tensorHom
      (𝟙 C) (ComonObj.counit (X := C))).f r =
      (C ◁ ComonObj.counit (X := C)).f r := rfl
  have hInner := tensor_desc_singleton_one f r s (by omega : r + (n + 0) = s)
  have hSignInner : (0 * r).negOnePow = (1 : ℤˣ) := by simp
  have hUnitorBridge : (ρ_ C).inv.f r = (HomologicalComplex.rightUnitor' C).inv r := rfl
  have hIotaBridge : HomologicalComplex.ιTensorObj C
      (HomologicalComplex.tensorUnit (ModuleCat R) (ComplexShape.up ℤ))
      r 0 r (by omega) =
      HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) r 0 r (add_zero r) := rfl
  have hCollapse : (HomologicalComplex.ιMapBifunctor C (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) r 0 r (add_zero r) ≫
      ((HomComplex.Cochain.tensor f
        (HomComplex.Cochain.ofHom (MonObj.one (X := A)))).v r s
        (by omega : r + (n + 0) = s) ≫ (MonObj.mul (X := A)).f s)) =
      (((0 * r).negOnePow •
        (f.v r (r + n) rfl ⊗ₘ
          (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl) ≫
        HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega)) ≫
        (MonObj.mul (X := A)).f s) := by
    rw [← Category.assoc, hInner.1]
  have hWhiskerA : (HomologicalComplex.tensorHom
      (𝟙 A) (MonObj.one (X := A))).f s =
      (A ◁ MonObj.one (X := A)).f s := rfl
  have hOneV : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) =
      (MonObj.one (X := A)).f 0 :=
    HomComplex.Cochain.ofHom_v _ _
  have hIotaOne := HomologicalComplex.ιTensorObj_tensorHom
    (𝟙 A) (MonObj.one (X := A)) (r + n) 0 s (by omega)
  have hIdA : ((𝟙 A : A ⟶ A).f (r + n)) = 𝟙 (A.X (r + n)) := rfl
  have hIdx : (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 (0 + 0) rfl =
      (HomComplex.Cochain.ofHom (MonObj.one (X := A))).v 0 0 (add_zero 0) := by
    congr 1
  have hIotaIdx : HomologicalComplex.ιTensorObj A A (r + n) (0 + 0) s (by omega) =
      HomologicalComplex.ιTensorObj A A (r + n) 0 s (by omega) := by
    congr 1
  have hFactor : (((f.v r (r + n) rfl ⊗ₘ
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0)))) =
      (((f.v r (r + n) rfl ⊗ₘ 𝟙 (𝟙_ (ModuleCat R))) ≫
        ((𝟙 (A.X (r + n))) ⊗ₘ
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0)))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have hSplit : ((((𝟙 (A.X (r + n))) ⊗ₘ
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv ≫ (MonObj.one (X := A)).f 0)))) =
      ((((𝟙 (A.X (r + n))) ⊗ₘ
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv) ≫
        ((𝟙 (A.X (r + n))) ⊗ₘ (MonObj.one (X := A)).f 0))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have hTail : ((((((𝟙 A : A ⟶ A).f (r + n) ⊗ₘ (MonObj.one (X := A)).f 0))) ≫
      (HomologicalComplex.ιTensorObj A A (r + n) 0 s (by omega) ≫
        (MonObj.mul (X := A)).f s))) =
      (HomologicalComplex.ιTensorObj A (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (r + n) 0 s (by omega) ≫
        ((HomologicalComplex.tensorHom (𝟙 A) (MonObj.one (X := A))).f s ≫
          (MonObj.mul (X := A)).f s)) := by
    rw [← Category.assoc, ← hIotaOne, Category.assoc]
  have hLamBridge : (ρ_ A).hom.f s = (HomologicalComplex.rightUnitor A).hom.f s := rfl
  have hStep : (HomologicalComplex.ιTensorObj A (𝟙_ (CochainComplex (ModuleCat R) ℤ))
        (r + n) 0 (r + n) (by omega) ≫
        (HomologicalComplex.rightUnitor A).hom.f (r + n)) =
      (((A.X (r + n) ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom) ≫ (ρ_ (A.X (r + n))).hom)) :=
    HomologicalComplex.ιTensorObj_rightUnitor_hom A (r + n)
  have hWhiskerS : ((A.X (r + n)) ◁
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).hom) =
      (𝟙 (A.X (r + n)) ⊗ₘ
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).hom) := rfl
  have hS : (((((𝟙 (A.X (r + n))) ⊗ₘ
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat R))).inv) ≫
      (((A.X (r + n)) ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat R))).hom) ≫ (ρ_ (A.X (r + n))).hom))) =
      (ρ_ (A.X (r + n))).hom) := by
    rw [hWhiskerS, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      Iso.inv_hom_id]
    simp
  have hWhiskerF : ((f.v r (r + n) rfl ⊗ₘ 𝟙 (𝟙_ (ModuleCat R)))) =
      ((f.v r (r + n) rfl ▷ 𝟙_ (ModuleCat R))) := rfl
  rw [eConv]
  rw [HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain _ _ _
    (show (n + 0) + 0 = n + 0 from add_zero _)]
  simp only [HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v] at hC_v hA_v ⊢
  rw [hMid_v] at ⊢
  rw [HomComplex.Cochain.zero_cochain_comp_v] at ⊢
  rw [HomComplex.Cochain.ofHom_v] at ⊢
  rw [hWhiskerCR] at ⊢
  simp only [← Category.assoc] at ⊢
  rw [hC_v] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hUnitorBridge] at ⊢
  rw [hU] at ⊢
  simp only [Category.assoc] at ⊢
  rw [hIotaBridge] at ⊢
  rw [hCollapse] at ⊢
  rw [hSignInner, one_smul] at ⊢
  rw [hIdx, hOneV] at ⊢
  nth_rewrite 2 [← Category.assoc] at ⊢
  rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc] at ⊢
  rw [hFactor] at ⊢
  rw [hSplit] at ⊢
  simp only [Category.assoc] at ⊢
  rw [← hIdA] at ⊢
  rw [hIotaIdx] at ⊢
  rw [hTail, hWhiskerA] at ⊢
  rw [hA_v] at ⊢
  rw [hIdA] at ⊢
  subst hrs
  rw [hLamBridge] at ⊢
  rw [hStep] at ⊢
  rw [hS] at ⊢
  rw [hWhiskerF] at ⊢
  rw [MonoidalCategory.rightUnitor_naturality] at ⊢
  simp at ⊢

end CochainComplex
