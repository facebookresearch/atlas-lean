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

public import MathlibExt.Analysis.CStarAlgebra.Module.Right
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Right C-star modules of continuous functions

The coefficient and vector carriers are the actual compact-domain continuous
function spaces, with their existing supremum norms. The two factories are
activated explicitly with local instances; importing this file installs no
scalar action, module dictionary, norm or completeness instance.

This constructs a function module, not the completed evaluation fibre of an
arbitrary module over an interval coefficient algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModule.ContinuousMap

universe uX uB uE

variable {B : Type uB} [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures. Let X be a
topological space.

Continuous B-valued functions act on continuous E-valued functions on the right by pointwise
coefficient multiplication.
-/
@[instance_reducible]
def rightAction (X : Type uX) [TopologicalSpace X] :
    SMul (C(X, B))ᵐᵒᵖ C(X, E) where
  smul b f :=
    { toFun := fun t => f t <• (MulOpposite.unop b) t
      continuous_toFun :=
        (_root_.CStarModule.continuous_right_smul (B := B) (E := E)).comp
          (f.continuous.prodMk (MulOpposite.unop b).continuous) }

/--
Let B be a possibly nonunital complex C*-algebra with a partial order on Bᵐᵒᵖ. Let E be a normed
right inner-product module over B, with compatible complex normed-space structures. Let X be a
topological space.

For f ∈ C(X, E), b ∈ C(X, B) and t ∈ X, the pointwise right action satisfies (fb)(t) = f(t)b(t).
-/
@[simp]
theorem right_smul_apply (X : Type uX) [TopologicalSpace X]
    (f : C(X, E)) (b : C(X, B)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) := rightAction (B := B) (E := E) X
     (f <• b) t = f t <• b t) :=
  rfl

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a normed right inner-product module over B, with
compatible complex normed-space structures. Let X be a compact topological space. Equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order.

The space C(X, E) is a right inner-product C*-module over C(X, B), with the supremum norm,
pointwise coefficient action and pointwise inner product.
-/
@[instance_reducible]
def cstarModule (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [StarOrderedRing Bᵐᵒᵖ]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ] :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) := rightAction (B := B) (E := E) X
     CStarModule (C(X, B))ᵐᵒᵖ C(X, E)) := by
  letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) := rightAction (B := B) (E := E) X
  let Q : C(X, E) → C(X, E) → C(X, B) := fun f g =>
    { toFun := fun t => _root_.CStarModule.rightInner (B := B) (f t) (g t)
      continuous_toFun :=
        (_root_.CStarModule.continuous_rightInner (B := B) (E := E)).comp
          (f.continuous.prodMk g.continuous) }
  let root : C(X, E) → C(X, Bᵐᵒᵖ) := fun f =>
    { toFun := fun t => CFC.sqrt (inner Bᵐᵒᵖ (f t) (f t))
      continuous_toFun :=
        CFC.continuousOn_sqrt.comp_continuous
          ((_root_.CStarModule.continuous_inner (A := Bᵐᵒᵖ) (E := E)).comp
            (f.continuous.prodMk f.continuous))
          (fun t => _root_.CStarModule.inner_self_nonneg
            (A := Bᵐᵒᵖ) (E := E) (x := f t)) }
  let p : C(X, E) → (C(X, B))ᵐᵒᵖ := fun f =>
    MulOpposite.op
      { toFun := fun t => MulOpposite.unop (root f t)
        continuous_toFun := MulOpposite.continuous_unop.comp (root f).continuous }
  have hrootNorm (f : C(X, E)) (t : X) :
      ‖(MulOpposite.unop (p f)) t‖ = ‖f t‖ := by
    change ‖MulOpposite.unop (CFC.sqrt (inner Bᵐᵒᵖ (f t) (f t)))‖ = ‖f t‖
    rw [MulOpposite.norm_unop,
      CFC.norm_sqrt (inner Bᵐᵒᵖ (f t) (f t))
        (_root_.CStarModule.inner_self_nonneg
          (A := Bᵐᵒᵖ) (E := E) (x := f t))]
    exact (_root_.CStarModule.norm_eq_sqrt_norm_inner_self
      (A := Bᵐᵒᵖ) (x := f t)).symm
  have hnorm (f : C(X, E)) : ‖p f‖ = ‖f‖ := by
    have h : ‖MulOpposite.unop (p f)‖ = ‖f‖ := by
      apply le_antisymm
      · apply (_root_.ContinuousMap.norm_le _ (norm_nonneg f)).2
        intro t
        rw [hrootNorm f t]
        exact f.norm_coe_le_norm t
      · apply (_root_.ContinuousMap.norm_le f
          (norm_nonneg (MulOpposite.unop (p f)))).2
        intro t
        rw [← hrootNorm f t]
        exact (MulOpposite.unop (p f)).norm_coe_le_norm t
    simpa only [MulOpposite.norm_unop] using h
  have hgram (f : C(X, E)) :
      star (p f) * p f = MulOpposite.op (Q f f) := by
    apply MulOpposite.unop_injective
    apply _root_.ContinuousMap.ext
    intro t
    let a : Bᵐᵒᵖ := inner Bᵐᵒᵖ (f t) (f t)
    change MulOpposite.unop (CFC.sqrt a) * star (MulOpposite.unop (CFC.sqrt a)) =
      MulOpposite.unop a
    have ha : 0 ≤ a :=
      _root_.CStarModule.inner_self_nonneg
        (A := Bᵐᵒᵖ) (E := E) (x := f t)
    have hs : star (CFC.sqrt a) = CFC.sqrt a :=
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
    have hmul : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [hs]
      exact CFC.sqrt_mul_sqrt_self a ha
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_star] using
      congrArg MulOpposite.unop hmul
  exact
    { inner := fun f g => MulOpposite.op (Q f g)
      inner_add_right := by
        intro f g h
        apply MulOpposite.unop_injective
        apply _root_.ContinuousMap.ext
        intro t
        change _root_.CStarModule.rightInner (B := B) (f t) (g t + h t) =
          _root_.CStarModule.rightInner (B := B) (f t) (g t) +
            _root_.CStarModule.rightInner (B := B) (f t) (h t)
        exact _root_.CStarModule.rightInner_add_right (f t) (g t) (h t)
      inner_self_nonneg := by
        intro f
        change (0 : (C(X, B))ᵐᵒᵖ) ≤ MulOpposite.op (Q f f)
        rw [← hgram f]
        exact star_mul_self_nonneg (p f)
      inner_self := by
        intro f
        constructor
        · intro h
          change MulOpposite.op (Q f f) = 0 at h
          apply _root_.ContinuousMap.ext
          intro t
          have hAt := congrArg
            (fun q : (C(X, B))ᵐᵒᵖ => (MulOpposite.unop q) t) h
          simp only [MulOpposite.unop_op, MulOpposite.unop_zero,
            _root_.ContinuousMap.zero_apply] at hAt
          change _root_.CStarModule.rightInner (B := B) (f t) (f t) = 0 at hAt
          apply (_root_.CStarModule.inner_self (A := Bᵐᵒᵖ) (x := f t)).mp
          apply MulOpposite.unop_injective
          simpa only [_root_.CStarModule.rightInner, MulOpposite.unop_zero] using hAt
        · intro h
          subst f
          apply MulOpposite.unop_injective
          apply _root_.ContinuousMap.ext
          intro t
          change _root_.CStarModule.rightInner (B := B) (0 : E) 0 = 0
          exact _root_.CStarModule.rightInner_zero_right 0
      inner_op_smul_right := by
        intro b f g
        apply MulOpposite.unop_injective
        apply _root_.ContinuousMap.ext
        intro t
        change _root_.CStarModule.rightInner (B := B) (f t)
            (g t <• (MulOpposite.unop b) t) =
          _root_.CStarModule.rightInner (B := B) (f t) (g t) *
            (MulOpposite.unop b) t
        exact _root_.CStarModule.rightInner_right_smul
          (f t) (g t) ((MulOpposite.unop b) t)
      inner_smul_right_complex := by
        intro c f g
        apply MulOpposite.unop_injective
        apply _root_.ContinuousMap.ext
        intro t
        change _root_.CStarModule.rightInner (B := B) (f t) (c • g t) =
          c • _root_.CStarModule.rightInner (B := B) (f t) (g t)
        exact _root_.CStarModule.rightInner_smul_right c (f t) (g t)
      star_inner := by
        intro f g
        apply MulOpposite.unop_injective
        apply _root_.ContinuousMap.ext
        intro t
        change star (_root_.CStarModule.rightInner (B := B) (f t) (g t)) =
          _root_.CStarModule.rightInner (B := B) (g t) (f t)
        exact _root_.CStarModule.star_rightInner (f t) (g t)
      norm_eq_sqrt_norm_inner_self := by
        intro f
        have hnormGram : ‖MulOpposite.op (Q f f)‖ = ‖f‖ ^ 2 := by
          calc
            _ = ‖star (p f) * p f‖ :=
                congrArg (fun z : (C(X, B))ᵐᵒᵖ => ‖z‖) (hgram f).symm
            _ = ‖p f‖ ^ 2 := by
              simpa only [pow_two] using CStarRing.norm_star_mul_self (x := p f)
            _ = ‖f‖ ^ 2 := congrArg (fun r : ℝ => r ^ 2) (hnorm f)
        rw [hnormGram, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)] }

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a normed right inner-product module over B, with
compatible complex normed-space structures. Let X be a compact topological space. Equip C(X,
B)ᵐᵒᵖ with a star-compatible partial order.

For f, g ∈ C(X, E) and t ∈ X, the coefficient-valued function ⟨f, g⟩ evaluates to ⟨f(t), g(t)⟩.
-/
@[simp]
theorem rightInner_apply (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [StarOrderedRing Bᵐᵒᵖ]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (f g : C(X, E)) (t : X) :
    (letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) := rightAction (B := B) (E := E) X
     letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) := cstarModule (B := B) (E := E) X
     (_root_.CStarModule.rightInner (B := C(X, B)) f g) t =
       _root_.CStarModule.rightInner (B := B) (f t) (g t)) :=
  rfl

end CStarModule.ContinuousMap
