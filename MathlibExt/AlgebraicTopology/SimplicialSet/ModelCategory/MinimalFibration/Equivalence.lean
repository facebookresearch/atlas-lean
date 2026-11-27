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
# Equivalence and functoriality of relative fiberwise simplex homotopy

For a Kan fibration p:X→S, fiberwise homotopy relative to ∂Δ[n] is an equivalence relation on
the n-simplices of X. Its witnesses are relative cylinder homotopies over the fixed base
n-simplex. Reflexivity uses a constant cylinder; fibration horn lifting gives reversal and
composition.

A commuting square of arrows sends fiberwise homotopies to homotopies of the image simplices.
Two degenerate simplices related by a boundary-stationary homotopy are equal, as their
nondegenerate epi factorizations are determined by their faces. The constructions use an
arbitrary simplicial-set universe u.

Reference: Goerss–Jardine, Simplicial Homotopy Theory, Chapter I, Section 10.
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

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval.
Regard this same cylinder as a relative homotopy of the simplex maps over p, retaining its
endpoints and boundary condition. -/
def toHomotopyRelOver (H : FiberwiseHomotopy (n := n) p x y) :
    SSet.HomotopyRelOver p (yonedaEquiv.symm x) (yonedaEquiv.symm y)
      (boundary n) where
  toHomotopyRel := H.homotopyRel
  over := H.over

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval. A
relative homotopy over p between the simplex maps of x,y gives the fiberwise simplex homotopy
with the same cylinder. -/
def ofHomotopyRelOver
    (H : SSet.HomotopyRelOver p (yonedaEquiv.symm x)
      (yonedaEquiv.symm y) (boundary n)) :
    FiberwiseHomotopy (n := n) p x y where
  homotopyRel := H.toHomotopyRel
  over := H.over

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval.
Converting a fiberwise witness to a relative-over-base witness and back recovers the original
witness. -/
@[simp]
lemma ofHomotopyRelOver_toHomotopyRelOver
    (H : FiberwiseHomotopy (n := n) p x y) :
    ofHomotopyRelOver H.toHomotopyRelOver = H := by
  rfl

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval.
Converting a relative-over-base witness to a fiberwise witness and back recovers that witness. -/
@[simp]
lemma toHomotopyRelOver_ofHomotopyRelOver
    (H : SSet.HomotopyRelOver p (yonedaEquiv.symm x)
      (yonedaEquiv.symm y) (boundary n)) :
    (ofHomotopyRelOver H).toHomotopyRelOver = H := by
  rfl

/-- For any simplicial map p:X→S and n-simplex x of X, the constant cylinder on x is a fiberwise
homotopy from x to itself, stationary on its boundary. -/
noncomputable def refl (p : X ⟶ S) (x : X _⦋n⦌) :
    FiberwiseHomotopy (n := n) p x x :=
  ofHomotopyRelOver
    (SSet.HomotopyRelOver.refl (yonedaEquiv.symm x) (boundary n) p)

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval. If
p is a Kan fibration, a fiberwise homotopy from x to y has a chosen reversed fiberwise homotopy
from y to x. -/
noncomputable def symm [Fibration p]
    (H : FiberwiseHomotopy (n := n) p x y) :
    FiberwiseHomotopy (n := n) p y x :=
  ofHomotopyRelOver (SSet.HomotopyRelOver.symm H.toHomotopyRelOver)

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval. If
p is a Kan fibration, homotopies from x to y and y to z compose to a fiberwise homotopy from x
to z, relative to their common boundary. -/
noncomputable def trans [Fibration p]
    (H₀₁ : FiberwiseHomotopy (n := n) p x y)
    (H₁₂ : FiberwiseHomotopy (n := n) p y z) :
    FiberwiseHomotopy (n := n) p x z :=
  ofHomotopyRelOver
    (SSet.HomotopyRelOver.trans H₀₁.toHomotopyRelOver H₁₂.toHomotopyRelOver)

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval. A
commuting square from p:X→S to p′:X′→S′ sends the witness to the fiberwise homotopy between the
images of x,y under its total-space map. -/
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

/-- For a Kan fibration p:X→S and each n∈ℕ, existence of fiberwise homotopies relative to ∂Δ[n] is
an equivalence relation on Xₙ. -/
theorem equivalence (p : X ⟶ S) [Fibration p] (n : ℕ) :
    _root_.Equivalence (FiberwiseHomotopic (n := n) p) where
  refl x := ⟨SSet.MinimalFibration.FiberwiseHomotopy.refl p x⟩
  symm := by
    rintro x y ⟨H⟩
    exact ⟨H.symm⟩
  trans := by
    rintro x y z ⟨H₀₁⟩ ⟨H₁₂⟩
    exact ⟨H₀₁.trans H₁₂⟩

/-- For any commuting square from p:X→S to p′:X′→S′, fiberwise homotopic n-simplices of X have
fiberwise homotopic images in X′. -/
lemma map {X' S' : SSet.{u}} {p' : X' ⟶ S'}
    (H : FiberwiseHomotopic (n := n) p x y)
    (f : Arrow.mk p ⟶ Arrow.mk p') :
    FiberwiseHomotopic (n := n) p' (f.left.app _ x) (f.left.app _ y) := by
  obtain ⟨H⟩ := H
  exact ⟨H.map f⟩

end FiberwiseHomotopic

/-- If two (n+1)-simplices of a simplicial set have the same codimension-one faces, then their
restrictions along any nonsurjective ordinal map [m]→[n+1] agree. -/
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

/-- If a degenerate N-simplex is expressed as the image of a nondegenerate m-simplex under an
epimorphism [N]→[m], then m<N. -/
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

/-- Let two (n+1)-simplices have the same faces and presentations by nondegenerate cores of
dimensions m₁,m₂. Assume the first ordinal map is epic and m₁<n+1; the second ordinal map may be
arbitrary. A section of the first map can be chosen so that its composite with the second is
monic and its induced restriction of the second core equals the first core. -/
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

/-- For an epi [n+1]→[m] with m<n+1 and any prescribed vertex j, there is a different vertex i whose
face inclusion followed by the epi is still epic. -/
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

/-- Two degenerate simplices of positive dimension with equal codimension-one faces are equal, by
their nondegenerate epi factorizations. -/
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

/-- For a simplicial map p:X→S and n-simplices x,y, a fiberwise simplex homotopy is a cylinder
Δ[n]×Δ[1]→X stationary on the boundary and projecting to p(x) independently of the interval. If
both x and y are degenerate, they are equal. Boundary stationarity gives all face equalities,
and the nondegenerate factorization determines the two degeneracies. -/
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
