/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialPrismSecondNondegenerateTriangle
public import MathlibExt.AlgebraicTopology.SimplicialObject.SplittingDegreeOne

/-!
# Degree-one polynomial prism maps and degeneracies

Let `P → const A` have a compatible polynomial splitting, let `Q → const A` be
additively aspherical, and let `f, g : P ⟶ Q` be augmented maps. The first and second
nondegenerate triangles are combined with the degenerate images of the zero-degree
edge `E` to give maps `H₀, H₁ : P₁ → Q₂`.

Their endpoint faces are `d₀ H₀ = g₁` and `d₂ H₁ = f₁`; the other exterior faces are
`d₂ H₀ = E d₁` and `d₀ H₁ = E d₀`, and their middle faces agree. Degeneracy
compatibility is `H₀ s₀ = s₁ E` and `H₁ s₀ = s₀ E`. Both maps have augmentation
equal to that of `P₁`. All algebra and polynomial-summand carriers have height
`max u v`, with the ground-ring and carrier universes independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialPrismDegreeOne

open PolynomialPrismFirstNondegenerateTriangle

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (f g : P ⟶ Q) (hQ : additiveResolutionCondition k A Q)

/--
The first triangle map `N₁ → Q₂`, obtained from the first polynomial triangle through
the polynomial presentation of the degree-one nondegenerate summand.
-/
def newFirst : s.splitting.N 1 ⟶ Q.left.obj (op ⦋2⦌) :=
  (s.polynomialIso 1).hom ≫ PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ

/--
The second triangle map `N₁ → Q₂`, obtained from the second polynomial triangle
through the polynomial presentation of the degree-one nondegenerate summand.
-/
def newSecond : s.splitting.N 1 ⟶ Q.left.obj (op ⦋2⦌) :=
  (s.polynomialIso 1).hom ≫ PolynomialPrismSecondNondegenerateTriangle.triangle s f g hQ

/--
The map `N₀ → Q₂` given by inclusion into `P₀`, the zero-degree base edge, and
the target degeneracy `s_i`, for `i : Fin 2`.
-/
def old (i : Fin 2) : s.splitting.N 0 ⟶ Q.left.obj (op ⦋2⦌) :=
  s.splitting.ι 0 ≫ baseEdge s f g hQ ≫ Q.left.σ i

/--
The map `P₁ → Q₂` obtained by degree-one coproduct descent from the first
nondegenerate triangle and the base edge followed by target degeneracy `s₁`.
-/
def first : P.left.obj (op ⦋1⦌) ⟶ Q.left.obj (op ⦋2⦌) :=
  s.splitting.oneDesc (old s f g hQ 1) (newFirst s f g hQ)

/--
The map `P₁ → Q₂` obtained by degree-one coproduct descent from the second
nondegenerate triangle and the base edge followed by target degeneracy `s₀`.
-/
def second : P.left.obj (op ⦋1⦌) ⟶ Q.left.obj (op ⦋2⦌) :=
  s.splitting.oneDesc (old s f g hQ 0) (newSecond s f g hQ)

@[reassoc]
private theorem first_new : s.splitting.ι 1 ≫ first s f g hQ = newFirst s f g hQ :=
  s.splitting.oneDesc_new _ _

@[reassoc]
private theorem second_new : s.splitting.ι 1 ≫ second s f g hQ = newSecond s f g hQ :=
  s.splitting.oneDesc_new _ _

@[reassoc]
private theorem first_old : (s.splitting.ι 0 ≫ P.left.σ (0 : Fin 1)) ≫ first s f g hQ = old s f g hQ 1 :=
  s.splitting.oneDesc_old _ _

@[reassoc]
private theorem second_old : (s.splitting.ι 0 ≫ P.left.σ (0 : Fin 1)) ≫ second s f g hQ = old s f g hQ 0 :=
  s.splitting.oneDesc_old _ _

private theorem coordinate_cancel {Z : CommAlgCat.{max u v} k}
    (q : P.left.obj (op ⦋1⦌) ⟶ Z) :
    (s.polynomialIso 1).hom ≫ (coordinate s ≫ q) = s.splitting.ι 1 ≫ q := by
  let F := CommAlgCat.of k (MvPolynomial (s.variables 1) k)
  let e : s.splitting.N 1 ≅ F := s.polynomialIso 1
  let c : F ⟶ P.left.obj (op ⦋1⦌) := coordinate s
  have hc : c = e.inv ≫ s.splitting.ι 1 := rfl
  have he : e.hom ≫ c = s.splitting.ι 1 :=
    (congrArg (fun z : F ⟶ P.left.obj (op ⦋1⦌) => e.hom ≫ z) hc).trans
      ((Category.assoc e.hom e.inv (s.splitting.ι 1)).symm.trans
        ((congrArg (fun z => z ≫ s.splitting.ι 1) e.hom_inv_id).trans (Category.id_comp _)))
  exact (Category.assoc e.hom c q).symm.trans (congrArg (fun z => z ≫ q) he)

private theorem polynomialTriangle_comp {Z : CommAlgCat.{max u v} k}
    (t : CommAlgCat.of k (MvPolynomial (s.variables 1) k) ⟶ Q.left.obj (op ⦋2⦌))
    (b : Q.left.obj (op ⦋2⦌) ⟶ Z) (q : P.left.obj (op ⦋1⦌) ⟶ Z)
    (h : t ≫ b = coordinate s ≫ q) :
    ((s.polynomialIso 1).hom ≫ t) ≫ b = s.splitting.ι 1 ≫ q :=
  (Category.assoc (s.polynomialIso 1).hom t b).trans
    ((congrArg (fun z => (s.polynomialIso 1).hom ≫ z) h).trans (coordinate_cancel s q))

@[reassoc]
private theorem newFirst_zero : newFirst s f g hQ ≫ Q.left.δ (0 : Fin 3) =
    s.splitting.ι 1 ≫ g.left.app (op ⦋1⦌) := by
  let t : CommAlgCat.of k (MvPolynomial (s.variables 1) k) ⟶ Q.left.obj (op ⦋2⦌) :=
    PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ
  have h : t ≫ Q.left.δ (0 : Fin 3) = coordinate s ≫ g.left.app (op ⦋1⦌) :=
    PolynomialPrismFirstNondegenerateTriangle.triangle_zero_face s f g hQ
  exact polynomialTriangle_comp s t (Q.left.δ (0 : Fin 3)) (g.left.app (op ⦋1⦌)) h

@[reassoc]
private theorem newFirst_last : newFirst s f g hQ ≫ Q.left.δ (2 : Fin 3) =
    s.splitting.ι 1 ≫ P.left.δ (1 : Fin 2) ≫ baseEdge s f g hQ := by
  let t : CommAlgCat.of k (MvPolynomial (s.variables 1) k) ⟶ Q.left.obj (op ⦋2⦌) :=
    PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ
  have h : t ≫ Q.left.δ (2 : Fin 3) =
      coordinate s ≫ (P.left.δ (1 : Fin 2) ≫ baseEdge s f g hQ) :=
    PolynomialPrismFirstNondegenerateTriangle.triangle_last_face s f g hQ
  exact polynomialTriangle_comp s t (Q.left.δ (2 : Fin 3))
    (P.left.δ (1 : Fin 2) ≫ baseEdge s f g hQ) h

@[reassoc]
private theorem newSecond_zero : newSecond s f g hQ ≫ Q.left.δ (0 : Fin 3) =
    s.splitting.ι 1 ≫ P.left.δ (0 : Fin 2) ≫ baseEdge s f g hQ := by
  let t : CommAlgCat.of k (MvPolynomial (s.variables 1) k) ⟶ Q.left.obj (op ⦋2⦌) :=
    PolynomialPrismSecondNondegenerateTriangle.triangle s f g hQ
  have h : t ≫ Q.left.δ (0 : Fin 3) =
      coordinate s ≫ (P.left.δ (0 : Fin 2) ≫ baseEdge s f g hQ) :=
    PolynomialPrismSecondNondegenerateTriangle.triangle_zero_face s f g hQ
  exact polynomialTriangle_comp s t (Q.left.δ (0 : Fin 3))
    (P.left.δ (0 : Fin 2) ≫ baseEdge s f g hQ) h

@[reassoc]
private theorem newSecond_last : newSecond s f g hQ ≫ Q.left.δ (2 : Fin 3) =
    s.splitting.ι 1 ≫ f.left.app (op ⦋1⦌) := by
  let t : CommAlgCat.of k (MvPolynomial (s.variables 1) k) ⟶ Q.left.obj (op ⦋2⦌) :=
    PolynomialPrismSecondNondegenerateTriangle.triangle s f g hQ
  have h : t ≫ Q.left.δ (2 : Fin 3) = coordinate s ≫ f.left.app (op ⦋1⦌) :=
    PolynomialPrismSecondNondegenerateTriangle.triangle_final_face s f g hQ
  exact polynomialTriangle_comp s t (Q.left.δ (2 : Fin 3)) (f.left.app (op ⦋1⦌)) h

@[reassoc]
private theorem new_middle : newSecond s f g hQ ≫ Q.left.δ (1 : Fin 3) =
    newFirst s f g hQ ≫ Q.left.δ (1 : Fin 3) := by
  let F := CommAlgCat.of k (MvPolynomial (s.variables 1) k)
  let e : s.splitting.N 1 ≅ F := s.polynomialIso 1
  let t₀ : F ⟶ Q.left.obj (op ⦋2⦌) := PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ
  let t₁ : F ⟶ Q.left.obj (op ⦋2⦌) := PolynomialPrismSecondNondegenerateTriangle.triangle s f g hQ
  have h : t₁ ≫ Q.left.δ (1 : Fin 3) = t₀ ≫ Q.left.δ (1 : Fin 3) :=
    PolynomialPrismSecondNondegenerateTriangle.middle_gluing s f g hQ
  exact (Category.assoc e.hom t₁ (Q.left.δ (1 : Fin 3))).trans
    ((congrArg (fun z : F ⟶ Q.left.obj (op ⦋1⦌) => e.hom ≫ z) h).trans
      (Category.assoc e.hom t₀ (Q.left.δ (1 : Fin 3))).symm)

/--
The zero face of the first degree-one prism map is the second endpoint component
`g₁ : P₁ → Q₁`.
-/
@[reassoc]
theorem first_zero_face : first s f g hQ ≫ Q.left.δ (0 : Fin 3) = g.left.app (op ⦋1⦌) := by
  apply CategoryTheory.SimplicialObject.Splitting.one_hom_ext s.splitting
  · rw [first_new_assoc, newFirst_zero]
  · rw [← Category.assoc, first_old s f g hQ]
    simp only [old, Category.assoc]
    have hcross : Q.left.σ (1 : Fin 2) ≫ Q.left.δ (0 : Fin 3) =
        Q.left.δ (0 : Fin 2) ≫ Q.left.σ (0 : Fin 1) := by
      have hc : (0 : Fin 2).castSucc = (0 : Fin 3) := Fin.ext rfl
      have hs : (0 : Fin 1).succ = (1 : Fin 2) := Fin.ext rfl
      simpa only [hc, hs] using Q.left.δ_comp_σ_of_le
        (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide)
    rw [hcross, baseEdge_zero_face_assoc s f g hQ]
    exact congrArg (fun z => s.splitting.ι 0 ≫ z)
      (SimplicialObject.σ_naturality g.left (0 : Fin 1)).symm

/--
The last face `d₂` of the second degree-one prism map is the first endpoint component
`f₁ : P₁ → Q₁`.
-/
@[reassoc]
theorem second_last_face : second s f g hQ ≫ Q.left.δ (2 : Fin 3) = f.left.app (op ⦋1⦌) := by
  apply CategoryTheory.SimplicialObject.Splitting.one_hom_ext s.splitting
  · rw [second_new_assoc, newSecond_last]
  · rw [← Category.assoc, second_old s f g hQ]
    simp only [old, Category.assoc]
    have hcross : Q.left.σ (0 : Fin 2) ≫ Q.left.δ (2 : Fin 3) =
        Q.left.δ (1 : Fin 2) ≫ Q.left.σ (0 : Fin 1) := by
      have hc : (0 : Fin 1).castSucc = (0 : Fin 2) := Fin.ext rfl
      have hs : (1 : Fin 2).succ = (2 : Fin 3) := Fin.ext rfl
      simpa only [hc, hs] using Q.left.δ_comp_σ_of_gt
        (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide)
    rw [hcross, baseEdge_one_face_assoc s f g hQ]
    exact congrArg (fun z => s.splitting.ι 0 ≫ z)
      (SimplicialObject.σ_naturality f.left (0 : Fin 1)).symm

/--
The zero face of the second degree-one prism is the source face `d₀ : P₁ → P₀`
followed by the zero-degree base edge.
-/
@[reassoc]
theorem second_zero_face : second s f g hQ ≫ Q.left.δ (0 : Fin 3) =
    P.left.δ (0 : Fin 2) ≫ baseEdge s f g hQ := by
  apply CategoryTheory.SimplicialObject.Splitting.one_hom_ext s.splitting
  · rw [second_new_assoc, newSecond_zero]
  · rw [← Category.assoc, second_old s f g hQ]
    simp only [old, Category.assoc]
    have hP : P.left.σ (0 : Fin 1) ≫ P.left.δ (0 : Fin 2) = 𝟙 _ :=
      P.left.δ_comp_σ_self' (i := (0 : Fin 1)) (j := (0 : Fin 2)) (Fin.ext rfl)
    have hPcomp : P.left.σ (0 : Fin 1) ≫ (P.left.δ (0 : Fin 2) ≫ baseEdge s f g hQ) =
        baseEdge s f g hQ :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ baseEdge s f g hQ) hP).trans (Category.id_comp _))
    rw [Q.left.δ_comp_σ_self' (i := (0 : Fin 2)) (j := (0 : Fin 3)) (Fin.ext rfl), hPcomp]
    simp only [Category.comp_id]

/--
The last face `d₂` of the first degree-one prism is the source face `d₁ : P₁ → P₀`
followed by the zero-degree base edge.
-/
@[reassoc]
theorem first_last_face : first s f g hQ ≫ Q.left.δ (2 : Fin 3) =
    P.left.δ (1 : Fin 2) ≫ baseEdge s f g hQ := by
  apply CategoryTheory.SimplicialObject.Splitting.one_hom_ext s.splitting
  · rw [first_new_assoc, newFirst_last]
  · rw [← Category.assoc, first_old s f g hQ]
    simp only [old, Category.assoc]
    have hP : P.left.σ (0 : Fin 1) ≫ P.left.δ (1 : Fin 2) = 𝟙 _ :=
      P.left.δ_comp_σ_succ' (i := (0 : Fin 1)) (j := (1 : Fin 2)) (Fin.ext rfl)
    have hPcomp : P.left.σ (0 : Fin 1) ≫ (P.left.δ (1 : Fin 2) ≫ baseEdge s f g hQ) =
        baseEdge s f g hQ :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ baseEdge s f g hQ) hP).trans (Category.id_comp _))
    rw [Q.left.δ_comp_σ_succ' (i := (1 : Fin 2)) (j := (2 : Fin 3)) (Fin.ext rfl), hPcomp]
    simp only [Category.comp_id]

/--
The first and second whole-source degree-one prisms have the same middle face `d₁`.
-/
@[reassoc]
theorem middle_gluing : second s f g hQ ≫ Q.left.δ (1 : Fin 3) = first s f g hQ ≫ Q.left.δ (1 : Fin 3) := by
  apply CategoryTheory.SimplicialObject.Splitting.one_hom_ext s.splitting
  · rw [second_new_assoc, first_new_assoc, new_middle]
  · rw [← Category.assoc, second_old s f g hQ, ← Category.assoc, first_old s f g hQ]
    simp only [old, Category.assoc]
    rw [Q.left.δ_comp_σ_succ' (i := (0 : Fin 2)) (j := (1 : Fin 3)) (Fin.ext rfl),
      Q.left.δ_comp_σ_self' (i := (1 : Fin 2)) (j := (1 : Fin 3)) (Fin.ext rfl)]

/--
The source degeneracy `s₀ : P₀ → P₁` followed by the first degree-one prism equals
the base edge followed by target degeneracy `s₁ : Q₁ → Q₂`.
-/
@[reassoc]
theorem first_degeneracy : P.left.σ (0 : Fin 1) ≫ first s f g hQ =
    baseEdge s f g hQ ≫ Q.left.σ (1 : Fin 2) := by
  letI : IsIso (s.splitting.ι 0) := by
    change IsIso s.splitting.zeroIso.hom
    infer_instance
  apply (cancel_epi (s.splitting.ι 0)).mp
  rw [← Category.assoc, first_old]
  rfl

/--
The source degeneracy `s₀ : P₀ → P₁` followed by the second degree-one prism equals
the base edge followed by target degeneracy `s₀ : Q₁ → Q₂`.
-/
@[reassoc]
theorem second_degeneracy : P.left.σ (0 : Fin 1) ≫ second s f g hQ =
    baseEdge s f g hQ ≫ Q.left.σ (0 : Fin 2) := by
  letI : IsIso (s.splitting.ι 0) := by
    change IsIso s.splitting.zeroIso.hom
    infer_instance
  apply (cancel_epi (s.splitting.ι 0)).mp
  rw [← Category.assoc, second_old]
  rfl

private theorem old_augmentation (i : Fin 2) : old s f g hQ i ≫ Q.hom.app (op ⦋2⦌) =
    (s.splitting.ι 0 ≫ P.left.σ (0 : Fin 1)) ≫ P.hom.app (op ⦋1⦌) := by
  have hQε : Q.left.σ i ≫ Q.hom.app (op ⦋2⦌) = Q.hom.app (op ⦋1⦌) :=
    (Q.hom.naturality (SimplexCategory.σ i).op).trans (Category.comp_id _)
  have hPε : P.left.σ (0 : Fin 1) ≫ P.hom.app (op ⦋1⦌) = P.hom.app (op ⦋0⦌) :=
    (P.hom.naturality (SimplexCategory.σ (0 : Fin 1)).op).trans (Category.comp_id _)
  simp only [old, Category.assoc]
  rw [hQε, baseEdge_augmentation, hPε]

/--
The first degree-one prism followed by the target augmentation `Q₂ → A` is the
source augmentation `P₁ → A`.
-/
@[reassoc]
theorem first_augmentation : first s f g hQ ≫ Q.hom.app (op ⦋2⦌) = P.hom.app (op ⦋1⦌) := by
  apply CategoryTheory.SimplicialObject.Splitting.one_hom_ext s.splitting
  · rw [first_new_assoc]
    let t : CommAlgCat.of k (MvPolynomial (s.variables 1) k) ⟶ Q.left.obj (op ⦋2⦌) :=
      PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ
    have h : t ≫ Q.hom.app (op ⦋2⦌) = coordinate s ≫ P.hom.app (op ⦋1⦌) :=
      PolynomialPrismFirstNondegenerateTriangle.triangle_augmentation s f g hQ
    exact polynomialTriangle_comp s t (Q.hom.app (op ⦋2⦌)) (P.hom.app (op ⦋1⦌)) h
  · rw [← Category.assoc, first_old s f g hQ, old_augmentation]

/--
The second degree-one prism followed by the target augmentation `Q₂ → A` is the
source augmentation `P₁ → A`.
-/
@[reassoc]
theorem second_augmentation : second s f g hQ ≫ Q.hom.app (op ⦋2⦌) = P.hom.app (op ⦋1⦌) := by
  apply CategoryTheory.SimplicialObject.Splitting.one_hom_ext s.splitting
  · rw [second_new_assoc]
    let t : CommAlgCat.of k (MvPolynomial (s.variables 1) k) ⟶ Q.left.obj (op ⦋2⦌) :=
      PolynomialPrismSecondNondegenerateTriangle.triangle s f g hQ
    have h : t ≫ Q.hom.app (op ⦋2⦌) = coordinate s ≫ P.hom.app (op ⦋1⦌) :=
      PolynomialPrismSecondNondegenerateTriangle.triangle_augmentation s f g hQ
    exact polynomialTriangle_comp s t (Q.hom.app (op ⦋2⦌)) (P.hom.app (op ⦋1⦌)) h
  · rw [← Category.assoc, second_old s f g hQ, old_augmentation]

end CommAlgCat.PolynomialPrismDegreeOne

end
