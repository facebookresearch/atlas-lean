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

public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Pullbacks of complex nonunital C-star algebras

The pullback of two complex nonunital C-star algebra homomorphisms is their
closed equalizer inside the product algebra. This file supplies the inherited
C-star structure, coordinate projections, universal lift, common-value map,
and the diagonal associated to a split cospan.
-/

@[expose] public section

open Set
open scoped CStarAlgebra

namespace NonUnitalCStarPullback

noncomputable section

universe uA uB uC uX

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [NonUnitalCStarAlgebra C]

/-- **Pullback of nonunital C*-homomorphisms.** Let `A,B,C` be nonunital complex C*-algebras and `f : A
→ C`, `g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) =
g(b)}`, with the inherited maximum norm. This equalizer is the pullback carrier inside the product
algebra. -/
abbrev Pullback (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :=
  NonUnitalStarAlgHom.equalizer
    (f.comp (NonUnitalStarAlgHom.fst ℂ A B))
    (g.comp (NonUnitalStarAlgHom.snd ℂ A B))

@[simp]
theorem mem_pullback (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) (p : A × B) :
    p ∈ Pullback f g ↔ f p.1 = g p.2 :=
  Iff.rfl

/-- **Closedness of a C*-pullback.** Let `A,B,C` be nonunital complex C*-algebras and `f : A → C`, `g :
B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) = g(b)}`, with
the inherited maximum norm. The pullback is closed in the norm topology of `A × B`. -/
theorem isClosed_pullback (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    IsClosed (Pullback f g : Set (A × B)) := by
  change IsClosed {p : A × B | f p.1 = g p.2}
  exact isClosed_eq
    ((map_continuous f).comp continuous_fst)
    ((map_continuous g).comp continuous_snd)

/-- The canonical inherited C-star structure on the closed pullback
subalgebra. -/
noncomputable instance instNonUnitalCStarAlgebra
    (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    NonUnitalCStarAlgebra (Pullback f g) := by
  let _ : IsClosed (Pullback f g : Set (A × B)) := isClosed_pullback f g
  exact NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (Pullback f g)

/-- **Element of a C*-pullback.** Let `A,B,C` be nonunital complex C*-algebras and `f : A → C`, `g : B →
C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) = g(b)}`, with the
inherited maximum norm. Any `a ∈ A`, `b ∈ B` satisfying `f(a) = g(b)` define the pullback element
`(a,b)`. -/
def mk (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (a : A) (b : B) (h : f a = g b) : Pullback f g :=
  ⟨(a, b), h⟩

@[simp]
theorem coe_mk (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (a : A) (b : B) (h : f a = g b) :
    ((mk f g a b h : Pullback f g) : A × B) = (a, b) :=
  rfl

/-- **First coordinate of a C*-pullback.** Let `A,B,C` be nonunital complex C*-algebras and `f : A → C`,
`g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) = g(b)}`,
with the inherited maximum norm. The first-coordinate function sends a pullback element `(a,b)` to
`a ∈ A`. -/
def fst (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) (p : Pullback f g) : A :=
  p.1.1

/-- **Second coordinate of a C*-pullback.** Let `A,B,C` be nonunital complex C*-algebras and `f : A →
C`, `g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) =
g(b)}`, with the inherited maximum norm. The second-coordinate function sends a pullback element
`(a,b)` to `b ∈ B`. -/
def snd (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) (p : Pullback f g) : B :=
  p.1.2

@[simp]
theorem fst_mk (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (a : A) (b : B) (h : f a = g b) : fst f g (mk f g a b h) = a :=
  rfl

@[simp]
theorem snd_mk (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (a : A) (b : B) (h : f a = g b) : snd f g (mk f g a b h) = b :=
  rfl

@[ext]
theorem ext (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    {p q : Pullback f g}
    (hfst : fst f g p = fst f g q) (hsnd : snd f g p = snd f g q) : p = q := by
  apply Subtype.ext
  exact Prod.ext hfst hsnd

/-- **First pullback projection.** Let `A,B,C` be nonunital complex C*-algebras and `f : A → C`, `g : B
→ C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) = g(b)}`, with
the inherited maximum norm. First-coordinate evaluation is a nonunital complex star homomorphism
from the pullback to `A`. -/
def fstHom (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    Pullback f g →⋆ₙₐ[ℂ] A where
  toFun := fst f g
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

/-- **Second pullback projection.** Let `A,B,C` be nonunital complex C*-algebras and `f : A → C`, `g : B
→ C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) = g(b)}`, with
the inherited maximum norm. Second-coordinate evaluation is a nonunital complex star homomorphism
from the pullback to `B`. -/
def sndHom (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    Pullback f g →⋆ₙₐ[ℂ] B where
  toFun := snd f g
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem fstHom_apply (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (p : Pullback f g) : fstHom f g p = fst f g p :=
  rfl

@[simp]
theorem sndHom_apply (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (p : Pullback f g) : sndHom f g p = snd f g p :=
  rfl

theorem continuous_fstHom (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    Continuous (fstHom f g) :=
  map_continuous (fstHom f g)

theorem continuous_sndHom (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    Continuous (sndHom f g) :=
  map_continuous (sndHom f g)

/-- **Compatibility of the pullback projections.** Let `A,B,C` be nonunital complex C*-algebras and `f :
A → C`, `g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) =
g(b)}`, with the inherited maximum norm. For every pullback element `p`, applying `f` to its first
projection equals applying `g` to its second projection. -/
@[simp]
theorem condition (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (p : Pullback f g) : f (fstHom f g p) = g (sndHom f g p) :=
  p.property

theorem condition_hom (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    f.comp (fstHom f g) = g.comp (sndHom f g) := by
  ext p
  exact condition f g p

/-! ## Universal property -/

variable {X : Type uX} [NonUnitalCStarAlgebra X]

/-- **Universal star homomorphism into a pullback.** Let `A,B,C` be nonunital complex C*-algebras and `f
: A → C`, `g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a)
= g(b)}`, with the inherited maximum norm. For another nonunital complex C*-algebra `X` and star
homomorphisms `u : X → A`, `v : X → B` with `f ∘ u = g ∘ v`, the map `x ↦ (u(x),v(x))` is a
nonunital complex star homomorphism into the pullback. -/
def lift (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (u : X →⋆ₙₐ[ℂ] A) (v : X →⋆ₙₐ[ℂ] B)
    (h : f.comp u = g.comp v) : X →⋆ₙₐ[ℂ] Pullback f g :=
  NonUnitalStarAlgHom.codRestrict (NonUnitalStarAlgHom.prod u v)
    (Pullback f g) fun x ↦
      (mem_pullback f g (u x, v x)).2 (DFunLike.congr_fun h x)

@[simp]
theorem coe_lift_apply (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (u : X →⋆ₙₐ[ℂ] A) (v : X →⋆ₙₐ[ℂ] B)
    (h : f.comp u = g.comp v) (x : X) :
    ((lift f g u v h x : Pullback f g) : A × B) = (u x, v x) :=
  rfl

@[simp]
theorem fstHom_comp_lift (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (u : X →⋆ₙₐ[ℂ] A) (v : X →⋆ₙₐ[ℂ] B)
    (h : f.comp u = g.comp v) :
    (fstHom f g).comp (lift f g u v h) = u := by
  ext x
  rfl

@[simp]
theorem sndHom_comp_lift (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (u : X →⋆ₙₐ[ℂ] A) (v : X →⋆ₙₐ[ℂ] B)
    (h : f.comp u = g.comp v) :
    (sndHom f g).comp (lift f g u v h) = v := by
  ext x
  rfl

/-- **Uniqueness from pullback coordinates.** Let `A,B,C` be nonunital complex C*-algebras and `f : A →
C`, `g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) =
g(b)}`, with the inherited maximum norm. For another nonunital complex C*-algebra `X`, two nonunital
star homomorphisms from `X` to the pullback are equal if their first and second projections agree. -/
theorem hom_ext (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (k l : X →⋆ₙₐ[ℂ] Pullback f g)
    (hfst : (fstHom f g).comp k = (fstHom f g).comp l)
    (hsnd : (sndHom f g).comp k = (sndHom f g).comp l) : k = l := by
  apply NonUnitalStarAlgHom.ext
  intro x
  apply ext f g
  · exact DFunLike.congr_fun hfst x
  · exact DFunLike.congr_fun hsnd x

/-- **Uniqueness of the universal pullback map.** Let `A,B,C` be nonunital complex C*-algebras and `f :
A → C`, `g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) =
g(b)}`, with the inherited maximum norm. For another nonunital complex C*-algebra `X`, a compatible
pair `u : X → A`, `v : X → B` of nonunital star homomorphisms has exactly one pullback homomorphism
with projections `u,v`. -/
theorem lift_unique (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (u : X →⋆ₙₐ[ℂ] A) (v : X →⋆ₙₐ[ℂ] B)
    (h : f.comp u = g.comp v) (k : X →⋆ₙₐ[ℂ] Pullback f g)
    (hfst : (fstHom f g).comp k = u)
    (hsnd : (sndHom f g).comp k = v) : k = lift f g u v h := by
  apply hom_ext f g
  · rw [fstHom_comp_lift, hfst]
  · rw [sndHom_comp_lift, hsnd]

/-! ## Split cospans -/

/-- **Common value homomorphism of a pullback.** Let `A,B,C` be nonunital complex C*-algebras and `f : A
→ C`, `g : B → C` nonunital complex star homomorphisms. Their pullback is `{(a,b) ∈ A × B : f(a) =
g(b)}`, with the inherited maximum norm. The common-value map `(a,b) ↦ f(a) = g(b)` is a nonunital
complex star homomorphism from the pullback to `C`. -/
def commonMap (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    Pullback f g →⋆ₙₐ[ℂ] C :=
  f.comp (fstHom f g)

@[simp]
theorem commonMap_apply (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C)
    (p : Pullback f g) : commonMap f g p = f (fst f g p) :=
  rfl

theorem commonMap_eq_right (f : A →⋆ₙₐ[ℂ] C) (g : B →⋆ₙₐ[ℂ] C) :
    commonMap f g = g.comp (sndHom f g) := by
  ext p
  exact condition f g p

/-- **Diagonal section into a pullback.** Let `A,B,C` be nonunital complex C*-algebras and let `r_A : A
→ C`, `r_B : B → C`, `i_A : C → A`, `i_B : C → B` be nonunital complex star homomorphisms with `r_A
∘ i_A = id` and `r_B ∘ i_B = id`. The map `c ↦ (i_A(c), i_B(c))` is a nonunital star homomorphism
from `C` to the pullback of `r_A` and `r_B`. -/
def diagonal (rA : A →⋆ₙₐ[ℂ] C) (rB : B →⋆ₙₐ[ℂ] C)
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (hA : rA.comp iA = NonUnitalStarAlgHom.id ℂ C)
    (hB : rB.comp iB = NonUnitalStarAlgHom.id ℂ C) :
    C →⋆ₙₐ[ℂ] Pullback rA rB :=
  lift rA rB iA iB (hA.trans hB.symm)

@[simp]
theorem fstHom_comp_diagonal
    (rA : A →⋆ₙₐ[ℂ] C) (rB : B →⋆ₙₐ[ℂ] C)
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (hA : rA.comp iA = NonUnitalStarAlgHom.id ℂ C)
    (hB : rB.comp iB = NonUnitalStarAlgHom.id ℂ C) :
    (fstHom rA rB).comp (diagonal rA rB iA iB hA hB) = iA :=
  fstHom_comp_lift rA rB iA iB _

@[simp]
theorem sndHom_comp_diagonal
    (rA : A →⋆ₙₐ[ℂ] C) (rB : B →⋆ₙₐ[ℂ] C)
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (hA : rA.comp iA = NonUnitalStarAlgHom.id ℂ C)
    (hB : rB.comp iB = NonUnitalStarAlgHom.id ℂ C) :
    (sndHom rA rB).comp (diagonal rA rB iA iB hA hB) = iB :=
  sndHom_comp_lift rA rB iA iB _

@[simp]
theorem commonMap_comp_diagonal
    (rA : A →⋆ₙₐ[ℂ] C) (rB : B →⋆ₙₐ[ℂ] C)
    (iA : C →⋆ₙₐ[ℂ] A) (iB : C →⋆ₙₐ[ℂ] B)
    (hA : rA.comp iA = NonUnitalStarAlgHom.id ℂ C)
    (hB : rB.comp iB = NonUnitalStarAlgHom.id ℂ C) :
    (commonMap rA rB).comp (diagonal rA rB iA iB hA hB) =
      NonUnitalStarAlgHom.id ℂ C := by
  rw [commonMap, NonUnitalStarAlgHom.comp_assoc, fstHom_comp_diagonal, hA]

end

end NonUnitalCStarPullback
