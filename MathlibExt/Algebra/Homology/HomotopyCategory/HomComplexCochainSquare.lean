/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# Naturality and square identities of homogeneous Hom cochains

In a preadditive category, complex maps give degree-zero Hom cochains and differentials give
degree-one Hom cochains. A complex map commutes with the two differential cochains, and each
differential cochain has square zero.

Composition of homogeneous cochains is bilinear. In particular the square of a sum of degree-one
endomorphism cochains expands into its four ordered products. No ring or monoidal structure on
the base category is needed.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex

namespace HomComplex.Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For f :
F → G, its degree-zero Hom cochain satisfies ofHom(f)·d_G=d_F·ofHom(f), where the product means
composition in source-to-target order. Equivalently d_G ∘ f=f ∘ d_F. -/
public theorem ofHom_comp_diff {F G : CochainComplex C ℤ} (f : F ⟶ G) :
    (ofHom f).comp (diff G) (zero_add 1) =
      (diff F).comp (ofHom f) (add_zero 1) := by
  apply ext
  intro r s hrs
  simp only [zero_cochain_comp_v, comp_zero_cochain_v, ofHom_v, diff_v]
  exact HomologicalComplex.Hom.comm f r s

/-- Let C be a preadditive category and F,G,H,K,L be integer-indexed cochain complexes in C. For
maps f : F → G, g : G → K and h : F → K with g ∘ f=h, the product of their degree-zero cochains
is ofHom(h). The resulting degree is zero. -/
public theorem ofHom_comp_of_eq {F G K : CochainComplex C ℤ}
    {f : F ⟶ G} {g : G ⟶ K} {h : F ⟶ K} (e : f ≫ g = h)
    (w : (0 : ℤ) + 0 = 0) :
    (ofHom f).comp (ofHom g) w = ofHom h := by
  rw [← ofHom_comp, e]

/-- Let C be preadditive and K an integer cochain complex. Its degree-one differential cochain
composes with itself to the zero degree-two cochain: d_K²=0. -/
public theorem diff_sq (K : CochainComplex C ℤ) (h : (1 : ℤ) + 1 = 2) :
    (diff K).comp (diff K) h = 0 := by
  refine ext _ _ ?_
  intro p q hpq
  simp only [comp_v _ _ h p _ q rfl (by omega), diff_v, zero_v]
  exact HomologicalComplex.d_comp_d K p (p + 1) q

/-- Let C be preadditive, X an integer cochain complex and f,g degree-one homogeneous endomorphism
cochains of X. Bilinearity gives (f+g)²=f²+fg+gf+g² as an equality of degree-two cochains, with
the order of each composition retained. -/
public theorem add_comp_self (X : CochainComplex C ℤ)
    (f g : Cochain X X 1) (h : (1 : ℤ) + 1 = 2) :
    (f + g).comp (f + g) h =
      (f.comp f h + f.comp g h) + (g.comp f h + g.comp g h) := by
  rw [CochainComplex.HomComplex.Cochain.add_comp,
    CochainComplex.HomComplex.Cochain.comp_add,
    CochainComplex.HomComplex.Cochain.comp_add]

end HomComplex.Cochain

end CochainComplex
