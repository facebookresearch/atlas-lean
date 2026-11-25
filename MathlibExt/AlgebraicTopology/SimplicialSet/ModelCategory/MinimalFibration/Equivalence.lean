/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.MapHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOver
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Equivalence and functoriality of simplex-level fiberwise homotopy

This module proves that the existing relation
`SSet.MinimalFibration.FiberwiseHomotopic p` is an equivalence relation when
`p` is a fibration. The proof converts its bundled witnesses to the existing
`SSet.HomotopyRelOver` API and reuses that API's reflexivity, symmetry, and
transitivity constructions.

It also gives functoriality along a morphism of arrows and the elementary
rigidity statement that two degenerate simplices related by such a homotopy
are equal. The rigidity proof is derived independently from Mathlib's
Eilenberg--Zilber factorization and uniqueness API: it compares the canonical
nondegenerate cores and then recovers the degeneracy maps pointwise from
their faces.

Mathematical source: the minimal-fibration strategy of Goerss--Jardine,
*Simplicial Homotopy Theory*, Chapter I, Section 10. No unpublished proof is
backported, and the obsolete internal-hom/fundamental-groupoid presentation
is not reproduced.

## Nonclaims

This file constructs no minimal subfibration, factorization, rigidity
isomorphism, weak equivalence, or model-category instance.
-/

@[expose] public section

open CategoryTheory Simplicial SSet HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet
namespace MinimalFibration

variable {X S : SSet.{u}}

namespace FiberwiseHomotopy

variable {p : X ⟶ S} {n : ℕ} {x y z : X _⦋n⦌}

/-- Regard a simplex-level fiberwise homotopy as a relative homotopy over the
base. This changes only the packaging: the cylinder, endpoints,
stationarity, and over-base equation are unchanged. -/
def toHomotopyRelOver (H : FiberwiseHomotopy (n := n) p x y) :
    SSet.HomotopyRelOver p (yonedaEquiv.symm x) (yonedaEquiv.symm y)
      (boundary n) where
  toHomotopyRel := H.homotopyRel
  over := H.over

/-- Package a relative homotopy over the base as the existing simplex-level
fiberwise homotopy. -/
def ofHomotopyRelOver
    (H : SSet.HomotopyRelOver p (yonedaEquiv.symm x)
      (yonedaEquiv.symm y) (boundary n)) :
    FiberwiseHomotopy (n := n) p x y where
  homotopyRel := H.toHomotopyRel
  over := H.over

@[simp]
lemma ofHomotopyRelOver_toHomotopyRelOver
    (H : FiberwiseHomotopy (n := n) p x y) :
    ofHomotopyRelOver H.toHomotopyRelOver = H := by
  rfl

@[simp]
lemma toHomotopyRelOver_ofHomotopyRelOver
    (H : SSet.HomotopyRelOver p (yonedaEquiv.symm x)
      (yonedaEquiv.symm y) (boundary n)) :
    (ofHomotopyRelOver H).toHomotopyRelOver = H := by
  rfl

/-- Reflexive simplex-level fiberwise homotopy. No fibration hypothesis is
needed. -/
noncomputable def refl (p : X ⟶ S) (x : X _⦋n⦌) :
    FiberwiseHomotopy (n := n) p x x :=
  ofHomotopyRelOver
    (SSet.HomotopyRelOver.refl (yonedaEquiv.symm x) (boundary n) p)

/-- Reverse a simplex-level fiberwise homotopy. -/
noncomputable def symm [Fibration p]
    (H : FiberwiseHomotopy (n := n) p x y) :
    FiberwiseHomotopy (n := n) p y x :=
  ofHomotopyRelOver (SSet.HomotopyRelOver.symm H.toHomotopyRelOver)

/-- Compose two simplex-level fiberwise homotopies. -/
noncomputable def trans [Fibration p]
    (H₀₁ : FiberwiseHomotopy (n := n) p x y)
    (H₁₂ : FiberwiseHomotopy (n := n) p y z) :
    FiberwiseHomotopy (n := n) p x z :=
  ofHomotopyRelOver
    (SSet.HomotopyRelOver.trans H₀₁.toHomotopyRelOver H₁₂.toHomotopyRelOver)

/-- Map a simplex-level fiberwise homotopy along a commutative square of
arrows. -/
def map {X' S' : SSet.{u}} {p' : X' ⟶ S'}
    (H : FiberwiseHomotopy (n := n) p x y)
    (f : Arrow.mk p ⟶ Arrow.mk p') :
    FiberwiseHomotopy (n := n) p' (f.left.app _ x) (f.left.app _ y) where
  homotopyRel :=
    { h := H.h ≫ f.left
      h₀ := by
        calc
          SSet.ι₀ ≫ (H.h ≫ f.left) = (SSet.ι₀ ≫ H.h) ≫ f.left := by
            rw [Category.assoc]
          _ = yonedaEquiv.symm x ≫ f.left := by rw [H.h₀]
          _ = yonedaEquiv.symm (f.left.app _ x) :=
            SSet.yonedaEquiv_symm_comp x f.left
      h₁ := by
        calc
          SSet.ι₁ ≫ (H.h ≫ f.left) = (SSet.ι₁ ≫ H.h) ≫ f.left := by
            rw [Category.assoc]
          _ = yonedaEquiv.symm y ≫ f.left := by rw [H.h₁]
          _ = yonedaEquiv.symm (f.left.app _ y) :=
            SSet.yonedaEquiv_symm_comp y f.left
      stationary := by
        intro m a ha t
        have hnat := ConcreteCategory.congr_hom
          (congr_app (SSet.yonedaEquiv_symm_comp x f.left) m) a
        change f.left.app m (H.h.app m ⟨a, t⟩) =
          (yonedaEquiv.symm (f.left.app _ x)).app m a
        rw [H.stationary a ha t]
        exact hnat }
  over := by
    have hw : f.left ≫ p' = p ≫ f.right := f.w
    calc
      (H.h ≫ f.left) ≫ p' = H.h ≫ (f.left ≫ p') :=
        Category.assoc _ _ _
      _ = H.h ≫ (p ≫ f.right) := by rw [hw]
      _ = (H.h ≫ p) ≫ f.right := (Category.assoc _ _ _).symm
      _ = (fst _ _ ≫ (yonedaEquiv.symm x ≫ p)) ≫ f.right := by
        rw [H.over]
      _ = fst _ _ ≫ ((yonedaEquiv.symm x ≫ p) ≫ f.right) :=
        Category.assoc _ _ _
      _ = fst _ _ ≫ (yonedaEquiv.symm x ≫ (p ≫ f.right)) := by
        rw [Category.assoc]
      _ = fst _ _ ≫ (yonedaEquiv.symm x ≫ (f.left ≫ p')) := by
        rw [← hw]
      _ = fst _ _ ≫ ((yonedaEquiv.symm x ≫ f.left) ≫ p') := by
        rw [Category.assoc]
      _ = fst _ _ ≫ (yonedaEquiv.symm (f.left.app _ x) ≫ p') := by
        rw [SSet.yonedaEquiv_symm_comp]

end FiberwiseHomotopy

namespace FiberwiseHomotopic

variable {p : X ⟶ S} {n : ℕ} {x y : X _⦋n⦌}

/-- Fiberwise homotopy of simplices is an equivalence relation when the base
map is a fibration. -/
theorem equivalence (p : X ⟶ S) [Fibration p] (n : ℕ) :
    _root_.Equivalence (FiberwiseHomotopic (n := n) p) where
  refl x := ⟨SSet.MinimalFibration.FiberwiseHomotopy.refl p x⟩
  symm := by
    rintro x y ⟨H⟩
    exact ⟨H.symm⟩
  trans := by
    rintro x y z ⟨H₀₁⟩ ⟨H₁₂⟩
    exact ⟨H₀₁.trans H₁₂⟩

/-- Map the existence of a simplex-level fiberwise homotopy along a
commutative square of arrows. -/
lemma map {X' S' : SSet.{u}} {p' : X' ⟶ S'}
    (H : FiberwiseHomotopic (n := n) p x y)
    (f : Arrow.mk p ⟶ Arrow.mk p') :
    FiberwiseHomotopic (n := n) p' (f.left.app _ x) (f.left.app _ y) := by
  obtain ⟨H⟩ := H
  exact ⟨H.map f⟩

end FiberwiseHomotopic

/-- Equality after all codimension-one faces implies equality after any map
whose image omits a vertex. -/
private lemma map_eq_of_face_eq
    {X : SSet.{u}} {n : ℕ} {x y : X _⦋n + 1⦌}
    (h : ∀ (i : Fin (n + 2)), X.δ i x = X.δ i y)
    {m : ℕ} (a : ⦋m⦌ ⟶ ⦋n + 1⦌)
    (ha : ¬ Function.Surjective a.toOrderHom) :
    X.map a.op x = X.map a.op y := by
  obtain ⟨i, a', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective a ha
  rw [op_comp, Functor.map_comp, comp_apply, comp_apply]
  change X.map a'.op (X.δ i x) = X.map a'.op (X.δ i y)
  rw [h i]

/-- In the nondegenerate factorization of a degenerate simplex, the core has
strictly smaller dimension. -/
private lemma nonDegenerate_dim_lt_of_degenerate
    {X : SSet.{u}} {N m : ℕ} {x : X _⦋N⦌}
    (hxdeg : x ∈ X.degenerate N) (f : ⦋N⦌ ⟶ ⦋m⦌) [Epi f]
    (x₀ : X.nonDegenerate m) (hx : x = X.map f.op x₀) : m < N := by
  obtain ⟨d, hd, g, hg, w, hw⟩ := (SSet.mem_degenerate_iff X x).mp hxdeg
  let : Epi g := hg
  obtain ⟨k, q, hq, z, hz⟩ := X.exists_nonDegenerate w
  let : Epi q := hq
  have hx' : x = X.map (g ≫ q).op z := by
    calc
      x = X.map g.op w := hw.symm
      _ = X.map g.op (X.map q.op z) := by rw [hz]
      _ = X.map (g ≫ q).op z := by
        rw [op_comp, Functor.map_comp]
        rfl
  have hmk : m = k :=
    X.unique_nonDegenerate_dim x f x₀ hx (g ≫ q) z hx'
  rw [hmk]
  exact lt_of_le_of_lt (SimplexCategory.le_of_epi q) hd

/-- Comparing all faces and then restricting along a section of the first
nondegenerate factorization embeds its core dimension in the second core
dimension. The returned equality is retained for the equal-dimension case. -/
private lemma exists_core_comparison
    {X : SSet.{u}} {n m₁ m₂ : ℕ} {x y : X _⦋n + 1⦌}
    (hface : ∀ (i : Fin (n + 2)), X.δ i x = X.δ i y)
    (f₁ : ⦋n + 1⦌ ⟶ ⦋m₁⦌) [Epi f₁]
    (x₀ : X.nonDegenerate m₁) (hx : x = X.map f₁.op x₀)
    (hm₁ : m₁ < n + 1) (f₂ : ⦋n + 1⦌ ⟶ ⦋m₂⦌)
    (y₀ : X.nonDegenerate m₂) (hy : y = X.map f₂.op y₀) :
    ∃ (s : SplitEpi f₁),
      (x₀ : X _⦋m₁⦌) = X.map (s.section_ ≫ f₂).op y₀ ∧
        Mono (s.section_ ≫ f₂) := by
  obtain ⟨⟨s⟩⟩ := isSplitEpi_of_epi f₁
  have hs : ¬ Function.Surjective s.section_.toOrderHom := by
    intro hsurj
    have : Epi s.section_ :=
      (SimplexCategory.epi_iff_surjective).2 hsurj
    have hle := SimplexCategory.len_le_of_epi s.section_
    change n + 1 ≤ m₁ at hle
    omega
  have hsection := map_eq_of_face_eq hface s.section_ hs
  have hxsection : X.map s.section_.op x = x₀ := by
    calc
      X.map s.section_.op x =
          X.map s.section_.op (X.map f₁.op x₀) := by rw [hx]
      _ = X.map (s.section_ ≫ f₁).op x₀ := by
        rw [op_comp, Functor.map_comp]
        rfl
      _ = x₀ := by simp
  have hysection : X.map s.section_.op y =
      X.map (s.section_ ≫ f₂).op y₀ := by
    rw [hy, op_comp, Functor.map_comp]
    rfl
  have hcore : (x₀ : X _⦋m₁⦌) = X.map (s.section_ ≫ f₂).op y₀ := by
    rw [← hysection, ← hsection, hxsection]
  have hmono : Mono (s.section_ ≫ f₂) :=
    X.mono_of_nonDegenerate x₀ (s.section_ ≫ f₂) y₀ hcore.symm
  exact ⟨s, hcore, hmono⟩

/-- An epi which strictly lowers dimension has two removable adjacent
vertices; hence one can be chosen away from any prescribed vertex. -/
private lemma exists_epi_face_ne
    {n m : ℕ} (f : ⦋n + 1⦌ ⟶ ⦋m⦌) [Epi f] (hm : m < n + 1)
    (j : Fin (n + 2)) :
    ∃ (i : Fin (n + 2)), i ≠ j ∧ Epi (SimplexCategory.δ i ≫ f) := by
  have hnot : ¬ Function.Injective f.toOrderHom := by
    intro hf
    have : Mono f := (SimplexCategory.mono_iff_injective).2 hf
    have hle := SimplexCategory.len_le_of_mono f
    change n + 1 ≤ m at hle
    omega
  obtain ⟨k, f', hfac⟩ :=
    SimplexCategory.eq_σ_comp_of_not_injective f hnot
  have hcomp : Epi (SimplexCategory.σ k ≫ f') := by
    rw [← hfac]
    infer_instance
  let : Epi f' := CategoryTheory.epi_of_epi (SimplexCategory.σ k) f'
  by_cases hj : (k.castSucc : Fin (n + 2)) = j
  · subst j
    refine ⟨k.succ, ne_of_gt Fin.castSucc_lt_succ, ?_⟩
    rw [hfac, ← Category.assoc, SimplexCategory.δ_comp_σ_succ,
      Category.id_comp]
    infer_instance
  · refine ⟨k.castSucc, hj, ?_⟩
    rw [hfac, ← Category.assoc, SimplexCategory.δ_comp_σ_self,
      Category.id_comp]
    infer_instance

/-- Degenerate simplices of positive dimension are determined by all their
faces. The proof compares their canonical nondegenerate factorizations and
then recovers the two epi maps pointwise. -/
private lemma eq_of_degenerate_of_face_eq
    {X : SSet.{u}} {n : ℕ} {x y : X _⦋n + 1⦌}
    (hxdeg : x ∈ X.degenerate (n + 1))
    (hydeg : y ∈ X.degenerate (n + 1))
    (hface : ∀ (i : Fin (n + 2)), X.δ i x = X.δ i y) : x = y := by
  obtain ⟨mₓ, fₓ, hfₓ, x₀, hx⟩ := X.exists_nonDegenerate x
  let : Epi fₓ := hfₓ
  obtain ⟨mᵧ, fᵧ, hfᵧ, y₀, hy⟩ := X.exists_nonDegenerate y
  let : Epi fᵧ := hfᵧ
  have hmₓ : mₓ < n + 1 :=
    nonDegenerate_dim_lt_of_degenerate hxdeg fₓ x₀ hx
  have hmᵧ : mᵧ < n + 1 :=
    nonDegenerate_dim_lt_of_degenerate hydeg fᵧ y₀ hy
  obtain ⟨sfₓ, hcore, hmonoₓᵧ⟩ :=
    exists_core_comparison hface fₓ x₀ hx hmₓ fᵧ y₀ hy
  obtain ⟨sfᵧ, _, hmonoᵧₓ⟩ :=
    exists_core_comparison (fun i ↦ (hface i).symm)
      fᵧ y₀ hy hmᵧ fₓ x₀ hx
  have hleₓᵧ : mₓ ≤ mᵧ := by
    let : Mono (sfₓ.section_ ≫ fᵧ) := hmonoₓᵧ
    exact SimplexCategory.len_le_of_mono (sfₓ.section_ ≫ fᵧ)
  have hleᵧₓ : mᵧ ≤ mₓ := by
    let : Mono (sfᵧ.section_ ≫ fₓ) := hmonoᵧₓ
    exact SimplexCategory.len_le_of_mono (sfᵧ.section_ ≫ fₓ)
  have hdim : mₓ = mᵧ := le_antisymm hleₓᵧ hleᵧₓ
  subst mᵧ
  let : Mono (sfₓ.section_ ≫ fᵧ) := hmonoₓᵧ
  have hcomp : sfₓ.section_ ≫ fᵧ = 𝟙 _ :=
    SimplexCategory.eq_id_of_mono _
  have hcoreVal : (x₀ : X _⦋mₓ⦌) = y₀ := by
    simpa [hcomp] using hcore
  have hcoreEq : x₀ = y₀ := Subtype.ext hcoreVal
  subst y₀
  have hmaps : fₓ = fᵧ := by
    ext j
    obtain ⟨i, hij, hi⟩ := exists_epi_face_ne fₓ hmₓ j
    let : Epi (SimplexCategory.δ i ≫ fₓ) := hi
    let z : X _⦋n⦌ := X.δ i x
    have hxface : z = X.map (SimplexCategory.δ i ≫ fₓ).op x₀ := by
      dsimp [z]
      rw [hx]
      change (X.map fₓ.op ≫ X.map (SimplexCategory.δ i).op) x₀ = _
      rw [← Functor.map_comp, ← op_comp]
    have hyface : z = X.map (SimplexCategory.δ i ≫ fᵧ).op x₀ := by
      dsimp [z]
      rw [hface i, hy]
      change (X.map fᵧ.op ≫ X.map (SimplexCategory.δ i).op) x₀ = _
      rw [← Functor.map_comp, ← op_comp]
    have hcompFace := X.unique_nonDegenerate_map z
      (SimplexCategory.δ i ≫ fₓ) x₀ hxface
      (SimplexCategory.δ i ≫ fᵧ) x₀ hyface
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
    have happ := SimplexCategory.congr_toOrderHom_apply hcompFace j'
    have hjmap : fₓ.toOrderHom j = fᵧ.toOrderHom j := by
      simpa [SimplexCategory.δ, hj'] using happ
    exact congrArg Fin.val hjmap
  rw [hx, hy, hmaps]

namespace FiberwiseHomotopy

variable {p : X ⟶ S} {n : ℕ} {x y : X _⦋n⦌}

/-- Degenerate simplices joined by a simplex-level fiberwise homotopy are
equal. This uses only stationarity on the boundary, not minimality or the
fibration hypothesis. -/
theorem eq_of_degenerate (H : FiberwiseHomotopy (n := n) p x y)
    (hx : x ∈ X.degenerate n) (hy : y ∈ X.degenerate n) : x = y := by
  obtain _ | n := n
  · simp at hx
  let W : OverRelation (n := n + 1) p x y :=
    { hom := H.homotopyRel
      base := yonedaEquiv.symm x ≫ p
      bd := (boundary (n + 1)).ι ≫ yonedaEquiv.symm x
      over := H.over
      boundary := rfl }
  have hbd := W.boundary_eq
  apply eq_of_degenerate_of_face_eq hx hy
  intro i
  have hi := boundary.ι i ≫= hbd
  rw [boundary.ι_ι_assoc, boundary.ι_ι_assoc] at hi
  apply yonedaEquiv.symm.injective
  simpa only [stdSimplex.δ_comp_yonedaEquiv_symm] using hi

end FiberwiseHomotopy

end MinimalFibration
end SSet
