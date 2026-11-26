/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import WantedExt.AlgebraicGeometry.FaltingsHeightWanted
import all WantedExt.AlgebraicGeometry.FaltingsHeightWanted

/-!
# The Gaudron–Rémond isogeny estimate

An explicit form of the isogeny theorem of Masser and Wüstholz: two isogenous abelian varieties
over a number field are related by isogenies whose degree is bounded explicitly in terms of the
dimension, the degree of the number field and the stable Faltings height.

Reference: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, Théorème 1.4, p. 2060, with $\kappa(A)$ defined on p. 2058,
<https://doi.org/10.1215/00127094-2782528>.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GaudronRemondIsogeny

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open WantedExt.AlgebraicGeometry.FaltingsHeight

universe u

/-- **Isogeny of abelian schemes.** Let $A$ and $B$ be abelian schemes over a scheme $S$. A
morphism $f : A \to B$ over $S$ is an isogeny if it is a homomorphism of group schemes and the
underlying morphism of schemes is finite, flat and surjective. Its degree is the rank of the
locally free $\mathcal{O}_B$-module $f_* \mathcal{O}_A$, which is the rank function
`Scheme.Hom.finrank` of the underlying morphism.

Over a field this is the usual notion: a surjective homomorphism of abelian varieties with finite
kernel is finite and flat. See J. S. Milne, *Abelian Varieties*, course notes, version 2.00
(2008), Chapter I, §7, <https://www.jmilne.org/math/CourseNotes/AV.pdf>. -/
def IsIsogeny {S : Scheme.{u}} {A B : AbelianScheme S} (f : A.model ⟶ B.model) : Prop :=
  IsMonHom f ∧ IsFinite f.left ∧ Flat f.left ∧ Surjective f.left

/-- **The Gaudron–Rémond constant.** For natural numbers $g$ and $d$ and a real number $h$,
$$\kappa(g, d, h) = \Bigl( (14 g)^{64 g^2} \, d \, \max(h, \log d, 1)^2 \Bigr)^{1024 g^3}.$$
For an abelian variety $A$ of dimension $g$ over a number field $k$, with $d = [k : \mathbb{Q}]$
and $h = h_F(A)$ its stable Faltings height, this is the constant
$\kappa(A) = \bigl( (14 g)^{64 g^2} [k : \mathbb{Q}] \max(h_F(A), \log [k : \mathbb{Q}], 1)^2
\bigr)^{\alpha(g)}$, $\alpha(g) = 2^{10} g^3$, of É. Gaudron and G. Rémond, *Polarisations et
isogénies*, Duke Math. J. 163 (2014), p. 2058, <https://doi.org/10.1215/00127094-2782528>. -/
def gaudronRemondKappa (g d : ℕ) (h : ℝ) : ℝ :=
  ((14 * g : ℝ) ^ (64 * g ^ 2) * d * (max (max h (Real.log d)) 1) ^ 2) ^ (1024 * g ^ 3)

/-- **Gaudron–Rémond isogeny estimate.** Let $k$ be a number field, $A$ an abelian variety of
dimension $g \ge 1$ over $k$ with stable Faltings height $h_F(A)$ (Faltings' normalization), and
$$\kappa(A) = \Bigl( (14 g)^{64 g^2} [k : \mathbb{Q}] \max\bigl(h_F(A), \log [k : \mathbb{Q}],
1\bigr)^2 \Bigr)^{1024 g^3}.$$
Let $K$ be any field extension of $k$ and $A'$ an abelian variety over $k$ such that $A_K$ and
$A'_K$ are isogenous. Then there are isogenies $\varphi_1 : A_K \to A'_K$ and
$\varphi_2 : A'_K \to A_K$ over $K$ whose degrees are at most $\kappa(A)$. The degree of an
isogeny is the rank of the finite flat morphism, which the statement bounds at every point of
the target.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, Théorème 1.4, p. 2060, with $\kappa(A)$ defined on p. 2058 and the degree of a pair
of isogenies on p. 2059, <https://doi.org/10.1215/00127094-2782528>. -/
public theorem_wanted exists_isogenies_degree_le_kappa (k : Type u) [Field k] [NumberField k]
    (A A' : AbelianScheme (Spec (CommRingCat.of k))) (g : ℕ) (hg : 1 ≤ g)
    [SmoothOfRelativeDimension g A.model.hom] (K : Type u) [Field K] [Algebra k K]
    (hiso : ∃ f : (fieldBaseChange K A).model ⟶ (fieldBaseChange K A').model, IsIsogeny f) :
    ∃ (φ₁ : (fieldBaseChange K A).model ⟶ (fieldBaseChange K A').model)
      (φ₂ : (fieldBaseChange K A').model ⟶ (fieldBaseChange K A).model),
      IsIsogeny φ₁ ∧ IsIsogeny φ₂ ∧
      (∀ y, (φ₁.left.finrank y : ℝ) ≤
        gaudronRemondKappa g (Module.finrank ℚ k) (❰faltingsHeight❱ k A)) ∧
      (∀ y, (φ₂.left.finrank y : ℝ) ≤
        gaudronRemondKappa g (Module.finrank ℚ k) (❰faltingsHeight❱ k A))

end WantedExt.AlgebraicGeometry.GaudronRemondIsogeny
