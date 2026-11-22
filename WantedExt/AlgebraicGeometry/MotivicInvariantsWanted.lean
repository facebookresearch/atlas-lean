/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Motivic invariants of birational maps

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.AlgebraicGeometry.MotivicInvariants` — annals_motivic_invariants (manifest `manifests/problems/annals_motivic_invariants.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.AlgebraicGeometry.MotivicInvariantsWanted` namespace. Mathematical
statements are unchanged. Source: H.-Y. Lin and E. Shinder, `Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-MotivicInvariants.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.MotivicInvariantsWanted
/-!
# Main Statement from Motivic invariants of birational maps

We formalise the statement of the main result from H.-Y. Lin and E. Shinder,
`Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024.
-/

set_option autoImplicit false

universe u

noncomputable section

end

end MathlibExt.AlgebraicGeometry.MotivicInvariantsWanted

section Mathlib

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory

/-- **Birational map.** Let $X$ and $Y$ be irreducible schemes. A birational map from $X$ to $Y$
consists of dominant rational maps $f \colon X \dashrightarrow Y$ and
$g \colon Y \dashrightarrow X$ that are mutually inverse: $g \circ f$ is the identity rational
map of $X$ and $f \circ g$ is the identity rational map of $Y$. -/
structure BirationalMap (X Y : Scheme.{u}) [IrreducibleSpace X] [IrreducibleSpace Y] where
  /-- The forward rational map of a birational map. -/
  hom : X ⤏ Y
  [isDominant_hom : hom.IsDominant]
  /-- The inverse rational map of a birational map. -/
  inv : Y ⤏ X
  [isDominant_inv : inv.IsDominant]
  hom_comp_inv_id : hom.comp inv = .id X := by grind
  inv_comp_hom_id : inv.comp hom = .id Y := by grind

attribute [instance] BirationalMap.isDominant_hom BirationalMap.isDominant_inv

attribute [simp, grind =] BirationalMap.hom_comp_inv_id BirationalMap.inv_comp_hom_id

namespace BirationalMap

variable {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

@[ext]
lemma ext (f g : X.BirationalMap Y) (e : f.hom = g.hom) : f = g := by
  suffices f.inv = g.inv by grind [BirationalMap]
  calc
    f.inv = f.inv.comp (g.hom.comp g.inv) := by grind
    _     = g.inv := by grind

variable (X) in
/-- **Identity birational map.** For an irreducible scheme $X$, the identity birational map of
$X$ has the identity rational map of $X$ as both its forward and its inverse map. -/
@[simps]
def refl : X.BirationalMap X where
  hom := RationalMap.id X
  inv := RationalMap.id X

/-- **Inverse birational map.** Let $X$ and $Y$ be irreducible schemes. The inverse of a
birational map from $X$ to $Y$ is the birational map from $Y$ to $X$ whose forward map is the
inverse rational map of the original and whose inverse map is its forward rational map. -/
@[simps]
def symm (f : X.BirationalMap Y) : Y.BirationalMap X where
  hom := f.inv
  inv := f.hom

/-- **Composition of birational maps.** Let $X$, $Y$ and $Z$ be irreducible schemes, let $f$ be a
birational map from $X$ to $Y$ and let $g$ be a birational map from $Y$ to $Z$. The composite of
$f$ and $g$ is the birational map from $X$ to $Z$ whose forward rational map is the forward map of
$f$ followed by the forward map of $g$, and whose inverse rational map is the inverse of $g$
followed by the inverse of $f$. -/
@[simps]
noncomputable def trans (f : X.BirationalMap Y) (g : Y.BirationalMap Z) :
    BirationalMap X Z where
  hom := f.hom.comp g.hom
  inv := g.inv.comp f.inv

theorem refl_trans (f : X.BirationalMap Y) : (refl X).trans f = f := by
  ext; simp

theorem trans_refl (f : X.BirationalMap Y) : f.trans (refl Y) = f := by
  ext; simp

theorem symm_trans_self_id (f : X.BirationalMap Y) : f.symm.trans f = refl Y := by
  ext; simp

theorem trans_assoc {W : Scheme.{u}} [IrreducibleSpace W]
    (f : X.BirationalMap Y) (g : Y.BirationalMap Z) (h : Z.BirationalMap W) :
    (f.trans g).trans h = f.trans (g.trans h) := by
  ext; simp only [BirationalMap.trans_hom, f.hom.comp_assoc]

noncomputable instance : Group (X.BirationalMap X) where
  one := refl X
  inv := symm
  mul := trans
  mul_assoc := trans_assoc
  one_mul := refl_trans
  mul_one := trans_refl
  inv_mul_cancel := symm_trans_self_id

/-- **Birational maps over a base.** Let $X$ and $Y$ be irreducible schemes over a scheme $S$.
A birational map from $X$ to $Y$ is over $S$ when its forward rational map
$X \dashrightarrow Y$ is compatible with the structure maps to $S$.

Its inverse rational map is then compatible with the structure maps to $S$ as well. -/
abbrev IsOver (S : Scheme.{u}) [X.Over S] [Y.Over S] (f : X.BirationalMap Y) : Prop :=
  f.hom.IsOver S

instance (S : Scheme.{u}) [X.Over S] [Y.Over S] (f : BirationalMap X Y) [hf : f.IsOver S] :
    f.inv.IsOver S := by
  simp [RationalMap.isOver_iff, ← RationalMap.isOver_iff.mp hf, ← RationalMap.comp_toRationalMap,
    ← RationalMap.comp_assoc]

end BirationalMap

variable {X Y : Scheme.{u}}

lemma PartialMap.id_domain : (PartialMap.id X).domain = ⊤ := rfl

lemma PartialMap.id_hom : (PartialMap.id X).hom = X.topIso.hom := by
  rw [Hom.toPartialMap_hom, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
instance isDominant_toPartialMap_hom (f : X.PartialIso Y) : IsDominant f.toPartialMap.hom := by
  dsimp only [PartialIso.toPartialMap_domain, PartialIso.toPartialMap_hom]
  have := Opens.isDominant_ι f.dense_target
  infer_instance

@[simp]
lemma Opens.morphismRestrict_ι {X : Scheme.{u}} (U : X.Opens) :
    U.ι ∣_ U = Scheme.homOfLE _ U.ι_preimage_self.le ≫ (⊤ : Opens U).ι := by
  simp [← cancel_mono U.ι]

set_option backward.isDefEq.respectTransparency.types false in
lemma PartialIso.toPartialMap_comp_symm [PreirreducibleSpace X] [Nonempty Y] (f : X.PartialIso Y) :
    f.toPartialMap.comp f.symm.toPartialMap =
      (PartialMap.id X).restrict f.source f.dense_source le_top := by
  ext1
  · change f.source.ι ''ᵁ f.iso.hom ⁻¹ᵁ f.target.ι ⁻¹ᵁ f.target = f.source
    rw [Opens.ι_preimage_self, Hom.preimage_top, Opens.ι_image_top]
  · change (f.source.ι.isoImage (f.iso.hom ⁻¹ᵁ f.target.ι ⁻¹ᵁ f.target)).inv ≫
      (f.iso.hom ≫ f.target.ι) ∣_ f.target ≫ f.iso.inv ≫ f.source.ι = _
    simp_rw [morphismRestrict_comp, Opens.morphismRestrict_ι, homOfLE_ι,
      morphismRestrict_ι, Category.assoc, Iso.hom_inv_id_assoc, Hom.isoImage_inv_ι, isoOfEq_hom,
      PartialMap.restrict_hom, PartialMap.id_domain, PartialMap.id_hom, topIso_hom, homOfLE_ι]
    exact (X.homOfLE_ι _).symm

set_option backward.isDefEq.respectTransparency.types false in
lemma PartialIso.symm_toPartialMap_comp [Nonempty X] [PreirreducibleSpace Y] (f : X.PartialIso Y) :
    f.symm.toPartialMap.comp f.toPartialMap =
      (PartialMap.id Y).restrict f.target f.dense_target le_top := by
  ext1
  · change f.target.ι ''ᵁ f.iso.inv ⁻¹ᵁ f.source.ι ⁻¹ᵁ f.source = f.target
    rw [Opens.ι_preimage_self, Hom.preimage_top, Opens.ι_image_top]
  · change (f.target.ι.isoImage (f.iso.inv ⁻¹ᵁ f.source.ι ⁻¹ᵁ f.source)).inv ≫
      (f.iso.inv ≫ f.source.ι) ∣_ f.source ≫ f.iso.hom ≫ f.target.ι = _
    simp_rw [morphismRestrict_comp, Opens.morphismRestrict_ι, homOfLE_ι,
      morphismRestrict_ι, Category.assoc, Iso.inv_hom_id_assoc, Hom.isoImage_inv_ι, isoOfEq_hom,
      PartialMap.restrict_hom, PartialMap.id_domain, PartialMap.id_hom, topIso_hom, homOfLE_ι]
    exact (Y.homOfLE_ι _).symm

variable [IrreducibleSpace X] [IrreducibleSpace Y]

variable (X) in
/-- **Birational automorphisms over a base.** Let $X$ be an irreducible scheme over a scheme
$S$. The birational automorphisms of $X$ over $S$ form the subgroup of the group of birational
self-maps of $X$ consisting of those birational maps whose forward rational map
$X \dashrightarrow X$ is compatible with the structure maps to $S$. -/
def birationalAutOver (S : Scheme.{u}) [X.Over S] : Subgroup (X.BirationalMap X) where
  carrier := { f | f.IsOver S }
  one_mem' := inferInstanceAs ((RationalMap.id X).IsOver S)
  mul_mem' {f g} (_ : f.IsOver S) (_ : g.IsOver S) := inferInstanceAs ((f.hom.comp g.hom).IsOver S)
  inv_mem' {f} (_ : f.IsOver S) := inferInstanceAs (f.inv.IsOver S)

instance (S : Scheme.{u}) [X.Over S] (f : birationalAutOver X S) :
    (f : X.BirationalMap X).IsOver S := f.2

/-- **Birational map of a partial isomorphism.** Let $X$ and $Y$ be irreducible schemes and let
$f$ be a partial isomorphism from $X$ to $Y$, that is, an isomorphism from a dense open subscheme
of $X$ onto a dense open subscheme of $Y$. The birational map from $X$ to $Y$ given by $f$ has as
forward map the rational map $X \dashrightarrow Y$ represented by $f$, and as inverse the rational
map $Y \dashrightarrow X$ represented by the inverse of $f$. -/
@[simps]
def PartialIso.toBirationalMap (f : X.PartialIso Y) : X.BirationalMap Y where
  hom := f.toRationalMap
  inv := f.symm.toRationalMap
  hom_comp_inv_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff,
      PartialIso.toPartialMap_comp_symm]
    apply PartialMap.restrict_equiv
  inv_comp_hom_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff,
      PartialIso.symm_toPartialMap_comp]
    apply PartialMap.restrict_equiv

end AlgebraicGeometry.Scheme

end Mathlib

namespace MathlibExt.AlgebraicGeometry.MotivicInvariantsWanted

universe u

namespace MotivicInvariants

open CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

variable (𝕜 𝔽 : Type) [Field 𝕜] [Field 𝔽]

/-- **Variety over a field.** Let $k$ be a field. A variety over $k$ is a scheme $X$ together with a
morphism $X \to \operatorname{Spec} k$ such that $X$ is integral (irreducible and reduced) and the
morphism is separated and of finite type (locally of finite type and quasi-compact). -/
class Variety (X : Scheme) where
  [over : X.Over (Spec (.of 𝕜))]
  [isIntegral : IsIntegral X]
  [isSeparated : IsSeparated (X ↘ Spec (.of 𝕜))]
  [locallyOfFiniteType: LocallyOfFiniteType (X ↘ Spec (.of 𝕜))]
  [quasicompact : QuasiCompact (X ↘ Spec (.of 𝕜))]

attribute [instance_reducible] Variety.over

attribute [instance] Variety.over Variety.isIntegral

noncomputable instance (n : ℕ) : Variety 𝕜 𝔸(Fin n; Spec (.of 𝕜)) where

/-- **Pseudo-isomorphism.** Let $X$ and $Y$ be schemes. A partial isomorphism from $X$ to $Y$,
that is, an isomorphism $U \cong V$ between dense open subschemes $U \subseteq X$ and
$V \subseteq Y$, is a pseudo-isomorphism if it is an isomorphism in codimension one: every
point of $X$ outside $U$ and every point of $Y$ outside $V$ has coheight at least $2$ in the
specialization order of points. -/
structure IsPseudoIso
    {X Y : Scheme.{u}} (i : PartialIso X Y) : Prop where
  codim_source : ∀ x ∉ i.source, 2 ≤ Order.coheight x
  codim_target : ∀ y ∉ i.target, 2 ≤ Order.coheight y

/-- **Pseudo-regularization of a birational automorphism.** Let $X$ be a variety over a field
$k$ and let $\varphi$ be a birational automorphism of $X$. A pseudo-regularization of $\varphi$
consists of a variety $X'$ over $k$, a birational map $\alpha \colon X \dashrightarrow X'$ over
$k$, and a partial isomorphism $\gamma$ from $X'$ to itself over $k$ that is a
pseudo-isomorphism, such that $\varphi = \alpha^{-1} \circ \gamma \circ \alpha$, where $\gamma$
is viewed as a birational map. -/
structure PseudoRegularization {X : Scheme} [Variety 𝕜 X] (φ : BirationalMap X X) where
  /-- An irreducible scheme birational to `X`. -/
  X' : Scheme
  /-- The scheme is a variety. -/
  [variety : Variety 𝕜 X']
  /-- The birational map `α : X ⤏ X'`. -/
  α : BirationalMap X X'
  [isOver_α : α.IsOver (Spec (.of 𝕜))]
  /-- The pseudo-automorphism of `X'`, namely an isomorphism in codimension one. -/
  γ : PartialIso X' X'
  [isOver_γ : γ.IsOver (X' ↘ (Spec (.of 𝕜))) (X' ↘ (Spec (.of 𝕜)))]
  isPseudoIso : IsPseudoIso γ
  cond : φ = (α.trans γ.toBirationalMap).trans α.symm

/-- **Pseudo-regularizable birational automorphism.** Let $X$ be a variety over a field $k$. A
birational automorphism $\varphi$ of $X$ is pseudo-regularizable if there exist a variety $X'$
over $k$, a birational map $\alpha \colon X \dashrightarrow X'$ over $k$, and a partial
isomorphism $\gamma$ from $X'$ to itself over $k$ that is a pseudo-isomorphism (an isomorphism
in codimension one), such that $\varphi = \alpha^{-1} \circ \gamma \circ \alpha$, where $\gamma$
is viewed as a birational map. The variety $X'$ need not be smooth or projective.

Source: H.-Y. Lin and E. Shinder, Motivic invariants of birational maps, Definition 4.1. -/
abbrev IsPseudoRegularizable
    {X : Scheme} [Variety 𝕜 X] (φ : BirationalMap X X) : Prop :=
  Nonempty (PseudoRegularization 𝕜 φ)

/-- **Cremona group.** For a field $k$ and $n \in \mathbb{N}$, the Cremona group
$\mathrm{Cr}_n(k)$ is the group of birational automorphisms of affine $n$-space
$\mathbb{A}^n_k$ over $\operatorname{Spec} k$. -/
abbrev Cr (n : ℕ) : Type := 𝔸(Fin n; Spec (.of 𝕜)).birationalAutOver (Spec (.of 𝕜))

/-- **Cremona group generated by pseudo-regularizable elements.** For a field $k$ and
$n \in \mathbb{N}$, this is the proposition that the Cremona group $\mathrm{Cr}_n(k)$ is
generated, as a group, by its pseudo-regularizable elements. -/
abbrev GenByPseudoRegularizable (n : ℕ) : Prop :=
  Subgroup.closure { f : Cr 𝕜 n | IsPseudoRegularizable 𝕜 f.1 } = ⊤

/--
**$\mathrm{Cr}_3$ of a number field is not generated by pseudo-regularizable elements.** Let $k$
be a number field. The Cremona group $\mathrm{Cr}_3(k)$, the group of birational automorphisms of
affine $3$-space over $k$, is not generated by its pseudo-regularizable elements.

This is Theorem 1.2 (1) (a) of Lin and Shinder.

Source: H.-Y. Lin and E. Shinder, `Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-MotivicInvariants.lean Via leanprover/lean-eval@38361be, problem `annals_motivic_invariants`.
-/
public theorem_wanted theorem_1_2_1_a [NumberField 𝕜] :
    ¬ GenByPseudoRegularizable 𝕜 3

/--
**$\mathrm{Cr}_3$ of a function field over a number field is not generated by pseudo-regularizable
elements.** Let $F$ be a number field and let $X$ be a variety over $F$ of positive dimension, with
function field $F(X)$. The Cremona group $\mathrm{Cr}_3(F(X))$, the group of birational
automorphisms of affine $3$-space over $F(X)$, is not generated by its pseudo-regularizable
elements.

This is Theorem 1.2 (1) (b) of Lin and Shinder.

Source: H.-Y. Lin and E. Shinder, `Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-MotivicInvariants.lean Via leanprover/lean-eval@38361be, problem `annals_motivic_invariants`.
-/
public theorem_wanted theorem_1_2_1_b [NumberField 𝔽] (X : Scheme) [Variety 𝔽 X]
    (hX : 0 < topologicalKrullDim X) :
    ¬ GenByPseudoRegularizable X.functionField 3

/--
**$\mathrm{Cr}_3$ of a function field over a finite field is not generated by pseudo-regularizable
elements.** Let $F$ be a finite field and let $X$ be a variety over $F$ of positive dimension, with
function field $F(X)$. The Cremona group $\mathrm{Cr}_3(F(X))$, the group of birational
automorphisms of affine $3$-space over $F(X)$, is not generated by its pseudo-regularizable
elements.

This is Theorem 1.2 (1) (c) of Lin and Shinder.

Source: H.-Y. Lin and E. Shinder, `Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-MotivicInvariants.lean Via leanprover/lean-eval@38361be, problem `annals_motivic_invariants`.
-/
public theorem_wanted theorem_1_2_1_c [Finite 𝔽] (X : Scheme) [Variety 𝔽 X]
    (hX : 0 < topologicalKrullDim X) :
    ¬ GenByPseudoRegularizable X.functionField 3

/--
**$\mathrm{Cr}_3$ of a function field over an algebraically closed field is not generated by
pseudo-regularizable elements.** Let $F$ be an algebraically closed field and let $X$ be a variety
over $F$ of positive dimension, with function field $F(X)$. The Cremona group
$\mathrm{Cr}_3(F(X))$, the group of birational automorphisms of affine $3$-space over $F(X)$, is
not generated by its pseudo-regularizable elements.

This is Theorem 1.2 (1) (d) of Lin and Shinder.

Source: H.-Y. Lin and E. Shinder, `Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-MotivicInvariants.lean Via leanprover/lean-eval@38361be, problem `annals_motivic_invariants`.
-/
public theorem_wanted theorem_1_2_1_d [IsAlgClosed 𝔽] (X : Scheme) [Variety 𝔽 X]
    (hX : 0 < topologicalKrullDim X) :
    ¬ GenByPseudoRegularizable X.functionField 3

/--
**$\mathrm{Cr}_n$ of a subfield of $\mathbb{C}$ is not generated by pseudo-regularizable
elements for $n \ge 4$.** Let $k$ be a subfield of $\mathbb{C}$ and let $n \ge 4$. The Cremona group
$\mathrm{Cr}_n(k)$, the group of birational automorphisms of affine $n$-space over $k$, is not
generated by its pseudo-regularizable elements.

This is Theorem 1.2 (2) of Lin and Shinder.

Source: H.-Y. Lin and E. Shinder, `Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-MotivicInvariants.lean Via leanprover/lean-eval@38361be, problem `annals_motivic_invariants`.
-/
public theorem_wanted theorem_1_2_2 {n : ℕ} (hn : 4 ≤ n) (𝕜 : Subfield ℂ) :
    ¬ GenByPseudoRegularizable 𝕜 n

/--
**$\mathrm{Cr}_n$ of an infinite field is not generated by pseudo-regularizable elements for
$n \ge 5$.** Let $k$ be an infinite field and let $n \ge 5$. The Cremona group $\mathrm{Cr}_n(k)$,
the group of birational automorphisms of affine $n$-space over $k$, is not generated by its
pseudo-regularizable elements.

This is Theorem 1.2 (3) of Lin and Shinder.

Source: H.-Y. Lin and E. Shinder, `Motivic invariants of birational maps`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-MotivicInvariants.lean Via leanprover/lean-eval@38361be, problem `annals_motivic_invariants`.
-/
public theorem_wanted theorem_1_2_3 {n : ℕ} (hn : 5 ≤ n) [Infinite 𝕜] :
    ¬ GenByPseudoRegularizable 𝕜 n

end MotivicInvariants

end MathlibExt.AlgebraicGeometry.MotivicInvariantsWanted
