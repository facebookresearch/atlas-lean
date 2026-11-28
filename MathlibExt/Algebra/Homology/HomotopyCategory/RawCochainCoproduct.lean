/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomComplexCoproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Homogeneous cochains from a coproduct of complexes

Let `D` be preadditive with `J`-indexed coproducts, and `F_j` integer
cochain complexes. Degreewise coproduct descent gives a homogeneous
cochain `⊕_j F_j → A` from any family of degree-`d` cochains on the
summands; no differential compatibility is required. Restriction to
summands and descent are inverse additive maps. Descent commutes with
the internal-Hom differential in arbitrary integer degrees, composition
of homogeneous cochains, and maps of coproduct families. Degree-zero
complex-map families descend to the ordinary coproduct map.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex.Cochain

universe u v w

variable {D : Type u} [Category.{v} D] [Preadditive D]
variable {J : Type w} [HasColimitsOfShape (Discrete J) D]
variable (F : J → CochainComplex D ℤ)

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. Any family `ψ_j : F_j → A` of
degree `d` descends to a
unique degree-`d` cochain from `⊕_j F_j` to `A`. -/
noncomputable def coproductDesc {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) : Cochain (∐ F) A d :=
  Cochain.mk fun p q hpq =>
    (isColimitOfPreserves
      (HomologicalComplex.eval D (ComplexShape.up ℤ) p)
      (colimit.isColimit (Discrete.functor F))).desc
      { pt := A.X q
        ι := Discrete.natTrans (fun j => (ψ j.as).v p q hpq) }

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. For `p+d=q`, the degree-`p`
injection of `F_j` followed by
the `(p,q)` component of the descended cochain equals the
corresponding component of `ψ_j`, including negative degrees. -/
theorem coproductDesc_ι_v {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (j : J)
    (p q : ℤ) (hpq : p + d = q) :
    (Sigma.ι F j).f p ≫ (coproductDesc F d ψ).v p q hpq =
      (ψ j).v p q hpq := by
  simp only [coproductDesc, mk_v]
  exact (isColimitOfPreserves
    (HomologicalComplex.eval D (ComplexShape.up ℤ) p)
    (colimit.isColimit (Discrete.functor F))).fac
      { pt := A.X q
        ι := Discrete.natTrans (fun i => (ψ i.as).v p q hpq) }
      (Discrete.mk j)

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. Precomposing the descended
degree-`d` cochain with the
complex injection of `F_j` recovers `ψ_j`. -/
theorem coproductDesc_ι {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (j : J) :
    (ofHom (Sigma.ι F j)).comp (coproductDesc F d ψ) (zero_add d) = ψ j := by
  apply Cochain.ext
  intro p q hpq
  simpa only [zero_cochain_comp_v, ofHom_v] using
    coproductDesc_ι_v F d ψ j p q hpq

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. For a complex map `g : X → F_j`,
restriction of the
descended cochain along `g` followed by the coproduct injection
equals precomposition of `ψ_j` by `g`. -/
theorem coproductDesc_ι_comp {A X : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (j : J) (g : X ⟶ F j) :
    (ofHom (g ≫ Sigma.ι F j)).comp (coproductDesc F d ψ) (zero_add d) =
      (ofHom g).comp (ψ j) (zero_add d) := by
  rw [ofHom_comp, comp_assoc_of_first_is_zero_cochain, coproductDesc_ι]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. A degree-`d` cochain on `⊕_j F_j`
whose restriction to every
summand equals `ψ_j` is the coproduct descent of that family. -/
theorem coproductDesc_unique {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (α : Cochain (∐ F) A d)
    (h : ∀ j : J, (ofHom (Sigma.ι F j)).comp α (zero_add d) = ψ j) :
    α = coproductDesc F d ψ := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  exact (h j).trans (coproductDesc_ι F d ψ j).symm

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. Descending the restrictions of any
degree-`d` cochain
`α : ⊕_j F_j → A` reconstructs `α`. -/
theorem coproductDesc_precomp {A : CochainComplex D ℤ} (d : ℤ)
    (α : Cochain (∐ F) A d) :
    coproductDesc F d
      (fun j => (ofHom (Sigma.ι F j)).comp α (zero_add d)) = α := by
  exact (coproductDesc_unique F d
    (fun j => (ofHom (Sigma.ι F j)).comp α (zero_add d)) α (fun _ => rfl)).symm

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. The family of zero degree-`d`
cochains descends to the
zero cochain on the coproduct. -/
theorem coproductDesc_zero {A : CochainComplex D ℤ} (d : ℤ) :
    coproductDesc F d (fun j => (0 : Cochain (F j) A d)) = 0 := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [coproductDesc_ι, Cochain.comp_zero]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. Descent is additive:
`desc(ψ+χ)=desc(ψ)+desc(χ)` for
families of the same homogeneous degree. -/
theorem coproductDesc_add {A : CochainComplex D ℤ} (d : ℤ)
    (ψ χ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d (fun j => ψ j + χ j) =
      coproductDesc F d ψ + coproductDesc F d χ := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [Cochain.comp_add, coproductDesc_ι, coproductDesc_ι, coproductDesc_ι]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. Descent preserves negatives:
`desc(-ψ)=-desc(ψ)`. -/
theorem coproductDesc_neg {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d (fun j => -(ψ j)) = -(coproductDesc F d ψ) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [Cochain.comp_neg, coproductDesc_ι, coproductDesc_ι]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. Descent preserves differences:
`desc(ψ-χ)=desc(ψ)-desc(χ)` for families of the same degree. -/
theorem coproductDesc_sub {A : CochainComplex D ℤ} (d : ℤ)
    (ψ χ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d (fun j => ψ j - χ j) =
      coproductDesc F d ψ - coproductDesc F d χ := by
  simp only [sub_eq_add_neg, coproductDesc_add, coproductDesc_neg]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. The descended cochain is zero if
and only if every
summand cochain `ψ_j` is zero. -/
theorem coproductDesc_eq_zero_iff {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    coproductDesc F d ψ = 0 ↔ ∀ j : J, ψ j = 0 := by
  constructor
  · intro h j
    have hj := congrArg
      (fun α : Cochain (∐ F) A d => (ofHom (Sigma.ι F j)).comp α (zero_add d)) h
    simpa only [coproductDesc_ι, Cochain.comp_zero] using hj
  · intro h
    have hψ : ψ = fun _ => 0 := funext h
    rw [hψ, coproductDesc_zero]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. For arbitrary integers `d,m`, the
internal-Hom differential
satisfies `δ_(d,m)(desc(ψ)) = desc(δ_(d,m)(ψ_j))`, including
nonconsecutive degrees where the differential is zero. -/
theorem coproductDesc_δ {A : CochainComplex D ℤ} (d m : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    HomComplex.δ d m (coproductDesc F d ψ) =
      coproductDesc F m (fun j => HomComplex.δ d m (ψ j)) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [← HomComplex.δ_ofHom_comp, coproductDesc_ι, coproductDesc_ι]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. For any integers `d,m`, the
differential of the descended
cochain vanishes if and only if the differential of every `ψ_j`
vanishes in that degree pair. -/
theorem coproductDesc_δ_eq_zero_iff {A : CochainComplex D ℤ} (d m : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    HomComplex.δ d m (coproductDesc F d ψ) = 0 ↔
      ∀ j : J, HomComplex.δ d m (ψ j) = 0 := by
  rw [coproductDesc_δ, coproductDesc_eq_zero_iff]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. For a homogeneous cochain `κ : A →
B` of degree `e`,
composition satisfies `desc(ψ_j ≫ κ)=desc(ψ) ≫ κ` in degree
`d+e`, without requiring either cochain to be closed. -/
theorem coproductDesc_comp {A B : CochainComplex D ℤ} (d e : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) (κ : Cochain A B e) :
    coproductDesc F (d + e) (fun j => (ψ j).comp κ rfl) =
      (coproductDesc F d ψ).comp κ rfl := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [coproductDesc_ι, ← comp_assoc_of_first_is_zero_cochain, coproductDesc_ι]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. For another family `G_j`, complex
maps `a_j : F_j → G_j`,
and degree-`d` cochains `ψ_j : G_j → A`, precomposing `desc_G(ψ)`
by the coproduct map `⊕ a_j` gives `desc_F(a_j ≫ ψ_j)`. -/
theorem coproductDesc_map {G : J → CochainComplex D ℤ}
    {A : CochainComplex D ℤ} (a : ∀ j : J, F j ⟶ G j) (d : ℤ)
    (ψ : ∀ j : J, Cochain (G j) A d) :
    (ofHom (CategoryTheory.Limits.Sigma.map a)).comp
        (coproductDesc G d ψ) (zero_add d) =
      coproductDesc F d (fun j => (ofHom (a j)).comp (ψ j) (zero_add d)) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [← comp_assoc_of_first_is_zero_cochain, ← ofHom_comp, Sigma.ι_map,
    coproductDesc_ι_comp, coproductDesc_ι]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. For complex maps `a_j : F_j → A`,
the descent of their
degree-zero homogeneous cochains is the homogeneous cochain of
the ordinary coproduct map `⊕_j F_j → A`. -/
theorem coproductDesc_ofHom {A : CochainComplex D ℤ}
    (a : ∀ j : J, F j ⟶ A) :
    coproductDesc F 0 (fun j => ofHom (a j)) = ofHom (Sigma.desc a) := by
  apply ext_of_precomp_sigma_ι _ _
  intro j
  rw [coproductDesc_ι, ← ofHom_comp, Sigma.ι_comp_desc]

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. Restriction gives an additive
equivalence between
 degree-`d` cochains `⊕_j F_j → A` and arbitrary families of
degree-`d` cochains `F_j → A`, with inverse degreewise descent. -/
noncomputable def coproductCochainEquiv (A : CochainComplex D ℤ) (d : ℤ) :
    Cochain (∐ F) A d ≃+ (∀ j : J, Cochain (F j) A d) where
  toFun α j := (ofHom (Sigma.ι F j)).comp α (zero_add d)
  invFun ψ := coproductDesc F d ψ
  left_inv α := coproductDesc_precomp F d α
  right_inv ψ := funext (fun j => coproductDesc_ι F d ψ j)
  map_add' α β := funext
    (fun j => Cochain.comp_add (ofHom (Sigma.ι F j)) α β (zero_add d))

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. The forward additive equivalence
takes a cochain `α` to
its family of restrictions `ι_j ≫ α` along the degree-zero
complex injections. -/
@[simp]
theorem coproductCochainEquiv_apply {A : CochainComplex D ℤ} (d : ℤ)
    (α : Cochain (∐ F) A d) (j : J) :
    coproductCochainEquiv F A d α j =
      (ofHom (Sigma.ι F j)).comp α (zero_add d) := rfl

/-- Let `D` be preadditive with coproducts indexed by a type `J`,
`F_j` a family of integer cochain complexes, and `A` another such
complex. A degree-`d` cochain is a homogeneous family of maps
`F_j^p → A^(p+d)`, without a differential-commutation condition. The inverse additive equivalence
takes the family `ψ_j`
to its degreewise coproduct descent. -/
@[simp]
theorem coproductCochainEquiv_symm_apply {A : CochainComplex D ℤ} (d : ℤ)
    (ψ : ∀ j : J, Cochain (F j) A d) :
    (coproductCochainEquiv F A d).symm ψ = coproductDesc F d ψ := rfl

end CochainComplex.HomComplex.Cochain

end
