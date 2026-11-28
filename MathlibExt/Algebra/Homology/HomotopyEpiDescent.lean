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

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Homotopy descent through a componentwise epimorphism

Let π : K → L be a morphism of complexes of arbitrary shape in a preadditive category, with
each component epic. Suppose endomorphisms f,g on K and f′,g′ on L commute with π. If a
homotopy H : f ≃ g has supplied factorizations π_i h̄(i,j) = H(i,j)π_j, then the components h̄
form a homotopy f′ ≃ g′.

The source and target category and degree-index universe levels are as stated.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory

universe w v u

namespace Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I : Type w} {c : ComplexShape I}

/-- A homotopy descends along epic components with supplied factorizations.

For the endpoint squares and component factorizations through π, the given h̄ components
satisfy the homotopy equations on L. -/
def descOfComponentwiseEpi
    {K L : HomologicalComplex C c}
    (pi : K ⟶ L) [∀ i, Epi (pi.f i)]
    {f g : K ⟶ K} {f' g' : L ⟶ L}
    (hf : f ≫ pi = pi ≫ f')
    (hg : g ≫ pi = pi ≫ g')
    (H : Homotopy f g)
    (hbar : ∀ i j, L.X i ⟶ L.X j)
    (fac : ∀ i j, pi.f i ≫ hbar i j = H.hom i j ≫ pi.f j) :
    Homotopy f' g' where
  hom := hbar
  zero i j hij := by
    apply (cancel_epi (pi.f i)).1
    rw [fac, H.zero i j hij, Limits.zero_comp, Limits.comp_zero]
  comm i := by
    have hfac :
        (fun i j => pi.f i ≫ hbar i j) =
          (fun i j => H.hom i j ≫ pi.f j) := by
      funext j k
      exact fac j k
    have hdNext : pi.f i ≫ dNext i hbar = dNext i H.hom ≫ pi.f i := by
      rw [← dNext_comp_left pi hbar i, hfac,
        dNext_comp_right H.hom pi i]
    have hprevD : pi.f i ≫ prevD i hbar = prevD i H.hom ≫ pi.f i := by
      rw [← prevD_comp_left pi hbar i, hfac,
        prevD_comp_right H.hom pi i]
    have hfi : f.f i ≫ pi.f i = pi.f i ≫ f'.f i := by
      simpa only [HomologicalComplex.comp_f] using
        congrArg (fun k => k.f i) hf
    have hgi : g.f i ≫ pi.f i = pi.f i ≫ g'.f i := by
      simpa only [HomologicalComplex.comp_f] using
        congrArg (fun k => k.f i) hg
    apply (cancel_epi (pi.f i)).1
    rw [← hfi, H.comm i]
    simp only [Preadditive.add_comp, Preadditive.comp_add]
    rw [hdNext, hprevD, ← hgi]

end Homotopy

end
