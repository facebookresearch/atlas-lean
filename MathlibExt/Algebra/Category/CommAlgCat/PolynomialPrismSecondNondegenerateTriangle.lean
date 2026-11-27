/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialPrismFirstNondegenerateTriangle

/-!
# Middle-face gluing for the second nondegenerate prism triangle

Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and s a compatible
polynomial splitting of P. Fix maps f,g:P→Q over A and assume that Q's normalized additive
augmentation is a quasi-isomorphism.

The second triangle uses the three edges c≫δ₀≫e, T₁≫δ₁ and c≫f₁ on the degree-one polynomial
coordinates, where e is the base prism and T₁ the first triangle. Their boundary compatibility
and augmentation equations permit a full-boundary filler T₂. In particular, T₂≫δ₁=T₁≫δ₁ is the
common-middle gluing equation.

The ground ring and algebra carrier parameters are independent. The augmented algebra diagrams
and their polynomial variable sets use the stable universe max(u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialPrismSecondNondegenerateTriangle

open PolynomialPrismFirstNondegenerateTriangle

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (f g : P ⟶ Q) (hQ : additiveResolutionCondition k A Q)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The zero edge of the second triangle is
c≫δ₀≫e:k[V₁]→Q₁, where c is the degree-one coordinate inclusion and e the base edge. -/
def zeroFace : (free.{u, v} k).obj (s.variables 1) ⟶ Q.left.obj (op ⦋1⦌) :=
  coordinate s ≫ P.left.δ (0 : Fin 2) ≫ baseEdge s f g hQ

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The middle edge k[V₁]→Q₁ is T₁≫δ₁, where
T₁:k[V₁]→Q₂ is the first nondegenerate triangle. -/
def middleFace : (free.{u, v} k).obj (s.variables 1) ⟶ Q.left.obj (op ⦋1⦌) :=
  PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ ≫ Q.left.δ (1 : Fin 3)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The final edge of the second triangle is
c≫f₁:k[V₁]→Q₁. -/
def finalFace : (free.{u, v} k).obj (s.variables 1) ⟶ Q.left.obj (op ⦋1⦌) :=
  coordinate s ≫ f.left.app (op ⦋1⦌)

private theorem pair_zero_middle : zeroFace s f g hQ ≫ Q.left.δ (0 : Fin 2) =
    middleFace s f g hQ ≫ Q.left.δ (0 : Fin 2) := by
  have hδ : Q.left.δ (0 : Fin 3) ≫ Q.left.δ (0 : Fin 2) =
      Q.left.δ (1 : Fin 3) ≫ Q.left.δ (0 : Fin 2) := by
    have hc : (0 : Fin 2).castSucc = (0 : Fin 3) := Fin.ext rfl
    have hs : (0 : Fin 2).succ = (1 : Fin 3) := Fin.ext rfl
    simpa only [hc, hs] using Q.left.δ_comp_δ_self (i := (0 : Fin 2))
  have hg : P.left.δ (0 : Fin 2) ≫ g.left.app (op ⦋0⦌) =
      g.left.app (op ⦋1⦌) ≫ Q.left.δ (0 : Fin 2) :=
    g.left.naturality (SimplexCategory.δ (0 : Fin 2)).op
  calc
    zeroFace s f g hQ ≫ Q.left.δ (0 : Fin 2) =
        coordinate s ≫ P.left.δ (0 : Fin 2) ≫ g.left.app (op ⦋0⦌) := by
      simp only [zeroFace, Category.assoc]
      rw [baseEdge_zero_face]
    _ = (coordinate s ≫ g.left.app (op ⦋1⦌)) ≫ Q.left.δ (0 : Fin 2) := by
      simpa only [Category.assoc] using congrArg (fun z => coordinate s ≫ z) hg
    _ = (PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ ≫ Q.left.δ (0 : Fin 3)) ≫
        Q.left.δ (0 : Fin 2) := by rw [triangle_zero_face, firstFace]
    _ = PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ ≫
        (Q.left.δ (1 : Fin 3) ≫ Q.left.δ (0 : Fin 2)) := by
      rw [Category.assoc, hδ]
    _ = middleFace s f g hQ ≫ Q.left.δ (0 : Fin 2) := by rw [middleFace, Category.assoc]

private theorem pair_zero_final : zeroFace s f g hQ ≫ Q.left.δ (1 : Fin 2) =
    finalFace s f ≫ Q.left.δ (0 : Fin 2) := by
  simp only [zeroFace, finalFace, Category.assoc]
  rw [baseEdge_one_face]
  have hf : P.left.δ (0 : Fin 2) ≫ f.left.app (op ⦋0⦌) =
      f.left.app (op ⦋1⦌) ≫ Q.left.δ (0 : Fin 2) :=
    f.left.naturality (SimplexCategory.δ (0 : Fin 2)).op
  exact congrArg (fun z => coordinate s ≫ z) hf

private theorem pair_middle_final : middleFace s f g hQ ≫ Q.left.δ (1 : Fin 2) =
    finalFace s f ≫ Q.left.δ (1 : Fin 2) := by
  have hδ : Q.left.δ (1 : Fin 3) ≫ Q.left.δ (1 : Fin 2) =
      Q.left.δ (2 : Fin 3) ≫ Q.left.δ (1 : Fin 2) := by
    have hc : (1 : Fin 2).castSucc = (1 : Fin 3) := Fin.ext rfl
    have hs : (1 : Fin 2).succ = (2 : Fin 3) := Fin.ext rfl
    simpa only [hc, hs] using Q.left.δ_comp_δ_self (i := (1 : Fin 2))
  have hf : P.left.δ (1 : Fin 2) ≫ f.left.app (op ⦋0⦌) =
      f.left.app (op ⦋1⦌) ≫ Q.left.δ (1 : Fin 2) :=
    f.left.naturality (SimplexCategory.δ (1 : Fin 2)).op
  calc
    middleFace s f g hQ ≫ Q.left.δ (1 : Fin 2) =
        PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ ≫
          (Q.left.δ (2 : Fin 3) ≫ Q.left.δ (1 : Fin 2)) := by
      rw [middleFace, Category.assoc, hδ]
    _ = (coordinate s ≫ P.left.δ (1 : Fin 2) ≫ baseEdge s f g hQ) ≫ Q.left.δ (1 : Fin 2) := by
      rw [← Category.assoc, triangle_last_face, lastFace]
    _ = coordinate s ≫ P.left.δ (1 : Fin 2) ≫ f.left.app (op ⦋0⦌) := by
      rw [Category.assoc, Category.assoc, baseEdge_one_face]
    _ = finalFace s f ≫ Q.left.δ (1 : Fin 2) := by
      simp only [finalFace, Category.assoc]
      rw [hf]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The second two-simplex boundary consists of the
zero edge c≫δ₀≫e, the middle edge T₁≫δ₁ and the final edge c≫f₁, indexed by Fin3. -/
def faces (j : Fin 3) : MvPolynomial (s.variables 1) k →ₐ[k] Q.left.obj (op ⦋1⦌) :=
  if j = 0 then (zeroFace s f g hQ).hom
  else if j = 1 then (middleFace s f g hQ).hom
  else (finalFace s f).hom

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. Face zero of the second boundary is c≫δ₀≫e. -/
@[simp]
theorem faces_zero : faces s f g hQ 0 = (zeroFace s f g hQ).hom := rfl

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. Face one of the second boundary is T₁≫δ₁, the
middle edge of the first triangle. -/
@[simp]
theorem faces_middle : faces s f g hQ 1 = (middleFace s f g hQ).hom := rfl

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. Face two of the second boundary is c≫f₁. -/
@[simp]
theorem faces_last : faces s f g hQ 2 = (finalFace s f).hom := rfl

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The three prescribed edges u₀,u₁,u₂ form a
two-simplex boundary: for j<l in Fin3, uⱼ≫δ(l−1)=uₗ≫δj. -/
theorem compatible : PolynomialBoundaryComparison.BoundaryCompatible k A Q (s.variables 1) 1
    (faces s f g hQ) := by
  intro j l hjl
  have hjBound : j.val ≤ 2 := Nat.le_of_lt_succ j.isLt
  have hlBound : l.val ≤ 2 := Nat.le_of_lt_succ l.isLt
  have hjlNat : j.val < l.val := hjl
  have hpairs : (j.val = 0 ∧ l.val = 1) ∨ (j.val = 0 ∧ l.val = 2) ∨
      (j.val = 1 ∧ l.val = 2) := by omega
  rcases hpairs with ⟨hjVal, hlVal⟩ | ⟨hjVal, hlVal⟩ | ⟨hjVal, hlVal⟩
  · have hjEq : j = 0 := Fin.ext (hjVal.trans (show (0 : Fin 3).val = 0 from rfl).symm)
    have hlEq : l = 1 := Fin.ext (hlVal.trans (show (1 : Fin 3).val = 1 from rfl).symm)
    subst j
    subst l
    have hp : (1 : Fin 3).pred (Fin.ne_zero_of_lt hjl) = (0 : Fin 2) := Fin.ext rfl
    have hc : (0 : Fin 3).castPred (Fin.ne_last_of_lt hjl) = (0 : Fin 2) := Fin.ext rfl
    simp only [hp, hc, faces_zero, faces_middle]
    exact congrArg CommAlgCat.Hom.hom (pair_zero_middle s f g hQ)
  · have hjEq : j = 0 := Fin.ext (hjVal.trans (show (0 : Fin 3).val = 0 from rfl).symm)
    have hlEq : l = 2 := Fin.ext (hlVal.trans (show (2 : Fin 3).val = 2 from rfl).symm)
    subst j
    subst l
    have hp : (2 : Fin 3).pred (Fin.ne_zero_of_lt hjl) = (1 : Fin 2) := Fin.ext rfl
    have hc : (0 : Fin 3).castPred (Fin.ne_last_of_lt hjl) = (0 : Fin 2) := Fin.ext rfl
    simp only [hp, hc, faces_zero, faces_last]
    exact congrArg CommAlgCat.Hom.hom (pair_zero_final s f g hQ)
  · have hjEq : j = 1 := Fin.ext (hjVal.trans (show (1 : Fin 3).val = 1 from rfl).symm)
    have hlEq : l = 2 := Fin.ext (hlVal.trans (show (2 : Fin 3).val = 2 from rfl).symm)
    subst j
    subst l
    have hp : (2 : Fin 3).pred (Fin.ne_zero_of_lt hjl) = (1 : Fin 2) := Fin.ext rfl
    have hc : (1 : Fin 3).castPred (Fin.ne_last_of_lt hjl) = (1 : Fin 2) := Fin.ext rfl
    simp only [hp, hc, faces_middle, faces_last]
    exact congrArg CommAlgCat.Hom.hom (pair_middle_final s f g hQ)

private theorem zeroFace_augmentation : zeroFace s f g hQ ≫ Q.hom.app (op ⦋1⦌) =
    coordinate s ≫ P.hom.app (op ⦋1⦌) := by
  have hε : P.left.δ (0 : Fin 2) ≫ P.hom.app (op ⦋0⦌) = P.hom.app (op ⦋1⦌) :=
    (P.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op).trans (Category.comp_id _)
  simp only [zeroFace, Category.assoc]
  rw [baseEdge_augmentation, hε]

private theorem middleFace_augmentation : middleFace s f g hQ ≫ Q.hom.app (op ⦋1⦌) =
    coordinate s ≫ P.hom.app (op ⦋1⦌) := by
  have hε : Q.left.δ (1 : Fin 3) ≫ Q.hom.app (op ⦋1⦌) = Q.hom.app (op ⦋2⦌) :=
    (Q.hom.naturality (SimplexCategory.δ (1 : Fin 3)).op).trans (Category.comp_id _)
  rw [middleFace, Category.assoc, hε, triangle_augmentation]

private theorem finalFace_augmentation : finalFace s f ≫ Q.hom.app (op ⦋1⦌) =
    coordinate s ≫ P.hom.app (op ⦋1⦌) := by
  rw [finalFace, Category.assoc]
  have hε : f.left.app (op ⦋1⦌) ≫ Q.hom.app (op ⦋1⦌) = P.hom.app (op ⦋1⦌) := by
    simpa only [NatTrans.comp_app] using NatTrans.congr_app f.w (op ⦋1⦌)
  exact congrArg (fun z => coordinate s ≫ z) hε

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. All three edges of the second boundary have the
common augmentation c≫εP:k[V₁]→A. -/
theorem faces_augmentation (j : Fin 3) :
    (Q.hom.app (op ⦋1⦌)).hom.comp (faces s f g hQ j) = augmentation s := by
  by_cases hzero : j = 0
  · subst j
    rw [faces_zero]
    exact congrArg CommAlgCat.Hom.hom (zeroFace_augmentation s f g hQ)
  · by_cases hone : j = 1
    · subst j
      rw [faces_middle]
      exact congrArg CommAlgCat.Hom.hom (middleFace_augmentation s f g hQ)
    · have hface : faces s f g hQ j = (finalFace s f).hom := by
        unfold faces
        exact (ite_eq_right hzero).trans (ite_eq_right hone)
      rw [hface]
      exact congrArg CommAlgCat.Hom.hom (finalFace_augmentation s f)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. Fill the compatible full boundary to obtain
T₂:k[V₁]→Q₂. Its faces are c≫δ₀≫e, T₁≫δ₁ and c≫f₁, with augmentation c≫εP. -/
def triangle : (free.{u, v} k).obj (s.variables 1) ⟶ Q.left.obj (op ⦋2⦌) :=
  CommAlgCat.ofHom (PolynomialBoundaryComparison.boundaryLift k A Q (s.variables 1) hQ 1
    (augmentation s) (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The second triangle satisfies T₂≫δ₀=c≫δ₀≫e. -/
@[reassoc]
theorem triangle_zero_face : triangle s f g hQ ≫ Q.left.δ (0 : Fin 3) = zeroFace s f g hQ := by
  apply CommAlgCat.hom_ext
  simp only [free, triangle, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
  exact (PolynomialBoundaryComparison.boundaryLift_faces k A Q (s.variables 1) hQ 1
    (augmentation s) (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ) 0).trans
      (faces_zero s f g hQ)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The first and second triangles satisfy T₂≫δ₁=T₁≫δ₁
as maps k[V₁]→Q₁. -/
@[reassoc]
theorem middle_gluing : triangle s f g hQ ≫ Q.left.δ (1 : Fin 3) =
    PolynomialPrismFirstNondegenerateTriangle.triangle s f g hQ ≫ Q.left.δ (1 : Fin 3) := by
  apply CommAlgCat.hom_ext
  change (triangle s f g hQ ≫ Q.left.δ (1 : Fin 3)).hom = (middleFace s f g hQ).hom
  simp only [free, triangle, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
  exact (PolynomialBoundaryComparison.boundaryLift_faces k A Q (s.variables 1) hQ 1
    (augmentation s) (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ) 1).trans
      (faces_middle s f g hQ)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The second triangle satisfies T₂≫δ₂=c≫f₁. -/
@[reassoc]
theorem triangle_final_face : triangle s f g hQ ≫ Q.left.δ (2 : Fin 3) = finalFace s f := by
  apply CommAlgCat.hom_ext
  simp only [free, triangle, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
  exact (PolynomialBoundaryComparison.boundaryLift_faces k A Q (s.variables 1) hQ 1
    (augmentation s) (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ) 2).trans
      (faces_last s f g hQ)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q augmentation-preserving maps. Assume that Q's normalized
additive augmentation is a quasi-isomorphism. The second triangle satisfies T₂≫εQ=c≫εP as
k-algebra maps k[V₁]→A. -/
@[reassoc]
theorem triangle_augmentation : triangle s f g hQ ≫ Q.hom.app (op ⦋2⦌) =
    coordinate s ≫ P.hom.app (op ⦋1⦌) := by
  apply CommAlgCat.hom_ext
  exact PolynomialBoundaryComparison.boundaryLift_augmentation k A Q (s.variables 1) hQ 1
    (augmentation s) (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ)

end CommAlgCat.PolynomialPrismSecondNondegenerateTriangle

end
