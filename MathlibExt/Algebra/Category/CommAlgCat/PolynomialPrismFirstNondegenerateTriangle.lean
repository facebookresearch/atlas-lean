/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialZeroGeneratedPrism
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialHornLift
public import MathlibExt.AlgebraicTopology.SimplicialObject.SplittingZeroIso
public import Mathlib.Tactic.FinCases

/-!
# First nondegenerate relative-prism triangle

Let k be a commutative ring and P,Q augmented simplicial k-algebras over A. A compatible
polynomial splitting of P gives polynomial coordinates on its nondegenerate summands. Assume
that Q's normalized additive augmentation is a quasi-isomorphism, and fix maps f,g:P→Q over A.

The degree-zero prism gives e:P₀→Q₁ with e≫δ₀=g₀, e≫δ₁=f₀ and e≫εQ=εP. On the degree-one
polynomial coordinates, c≫g₁ and c≫δ₁≫e form an inner horn missing face one. Filling it produces
a triangle in Q₂ with those exterior faces and the coordinate augmentation.

The ground-ring universe u and algebra carrier parameter v are independent. The algebra diagrams
and the chosen variable sets use the stable carrier universe max(u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialPrismFirstNondegenerateTriangle

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (f g : P ⟶ Q) (hQ : additiveResolutionCondition k A Q)

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the degree-zero nondegenerate summand N₀(P) has an algebra edge to Q₁. Its zero and one
faces are the restrictions of g₀ and f₀, and it preserves augmentation. -/
def zeroEdge : s.splitting.N 0 ⟶ Q.left.obj (op ⦋1⦌) :=
  PolynomialConstantSourcePrism.edge (s.variables 0) (s.polynomialIso 0)
    (PolynomialZeroGeneratedPrism.inclusion s ≫ f)
    (PolynomialZeroGeneratedPrism.inclusion s ≫ g) hQ

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, transport the edge on N₀(P) through the canonical degree-zero splitting isomorphism to
obtain e:P₀→Q₁. The face equations are e≫δ₀=g₀ and e≫δ₁=f₀. -/
def baseEdge : P.left.obj (op ⦋0⦌) ⟶ Q.left.obj (op ⦋1⦌) :=
  s.splitting.zeroIso.inv ≫ zeroEdge s f g hQ

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the base edge e:P₀→Q₁ satisfies e≫δ₀=g₀. -/
@[reassoc]
theorem baseEdge_zero_face : baseEdge s f g hQ ≫ Q.left.δ (0 : Fin 2) = g.left.app (op ⦋0⦌) := by
  have hface : zeroEdge s f g hQ ≫ Q.left.δ (0 : Fin 2) =
      ((PolynomialZeroGeneratedPrism.inclusion s ≫ g).left).app (op ⦋0⦌) :=
    PolynomialConstantSourcePrism.edge_zero_face
      (α := (PolynomialZeroGeneratedPrism.point s).hom) (s.variables 0) (s.polynomialIso 0)
      (PolynomialZeroGeneratedPrism.inclusion s ≫ f)
      (PolynomialZeroGeneratedPrism.inclusion s ≫ g) hQ
  rw [baseEdge, Category.assoc, hface]
  change s.splitting.zeroIso.inv ≫
    ((PolynomialZeroGeneratedPrism.inclusion s).left.app (op ⦋0⦌) ≫ g.left.app (op ⦋0⦌)) = _
  rw [PolynomialZeroGeneratedPrism.inclusion_zero, ← Category.assoc]
  have hzero : s.splitting.zeroIso.inv ≫ s.splitting.ι 0 = 𝟙 _ :=
    s.splitting.zeroIso.inv_hom_id
  rw [hzero, Category.id_comp]

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the base edge e:P₀→Q₁ satisfies e≫δ₁=f₀. -/
@[reassoc]
theorem baseEdge_one_face : baseEdge s f g hQ ≫ Q.left.δ (1 : Fin 2) = f.left.app (op ⦋0⦌) := by
  have hface : zeroEdge s f g hQ ≫ Q.left.δ (1 : Fin 2) =
      ((PolynomialZeroGeneratedPrism.inclusion s ≫ f).left).app (op ⦋0⦌) :=
    PolynomialConstantSourcePrism.edge_one_face
      (α := (PolynomialZeroGeneratedPrism.point s).hom) (s.variables 0) (s.polynomialIso 0)
      (PolynomialZeroGeneratedPrism.inclusion s ≫ f)
      (PolynomialZeroGeneratedPrism.inclusion s ≫ g) hQ
  rw [baseEdge, Category.assoc, hface]
  change s.splitting.zeroIso.inv ≫
    ((PolynomialZeroGeneratedPrism.inclusion s).left.app (op ⦋0⦌) ≫ f.left.app (op ⦋0⦌)) = _
  rw [PolynomialZeroGeneratedPrism.inclusion_zero, ← Category.assoc]
  have hzero : s.splitting.zeroIso.inv ≫ s.splitting.ι 0 = 𝟙 _ :=
    s.splitting.zeroIso.inv_hom_id
  rw [hzero, Category.id_comp]

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the base edge e:P₀→Q₁ satisfies e≫εQ=εP, where εP and εQ are the augmentations in
degrees zero and one. -/
@[reassoc]
theorem baseEdge_augmentation : baseEdge s f g hQ ≫ Q.hom.app (op ⦋1⦌) = P.hom.app (op ⦋0⦌) := by
  have hε : Q.left.δ (0 : Fin 2) ≫ Q.hom.app (op ⦋0⦌) = Q.hom.app (op ⦋1⦌) :=
    (Q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op).trans (Category.comp_id _)
  rw [← hε, ← Category.assoc, baseEdge_zero_face]
  simpa only [NatTrans.comp_app] using NatTrans.congr_app g.w (op ⦋0⦌)

/-- For a commutative ring k and an augmented simplicial k-algebra P over a commutative k-algebra A,
with compatible polynomial splitting s, let V₁ be the chosen variables of N₁(P). The coordinate
map k[V₁]→P₁ is the inverse polynomial presentation followed by the nondegenerate summand
inclusion. -/
def coordinate : (free.{u, v} k).obj (s.variables 1) ⟶ P.left.obj (op ⦋1⦌) :=
  (s.polynomialIso 1).inv ≫ s.splitting.ι 1

/-- For a commutative ring k and an augmented simplicial k-algebra P over a commutative k-algebra A,
with compatible polynomial splitting s, the augmentation k[V₁]→A on the degree-one variables is
the coordinate inclusion into P₁ followed by εP in degree one. -/
def augmentation : MvPolynomial (s.variables 1) k →ₐ[k] A :=
  (coordinate s ≫ P.hom.app (op ⦋1⦌)).hom

/-- For a commutative ring k and augmented simplicial k-algebras P,Q over A, a compatible polynomial
splitting s of P and a map g:P→Q over A, the first prescribed edge k[V₁]→Q₁ is the degree-one
coordinate inclusion c followed by g₁. -/
def firstFace : (free.{u, v} k).obj (s.variables 1) ⟶ Q.left.obj (op ⦋1⦌) :=
  coordinate s ≫ g.left.app (op ⦋1⦌)

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the last prescribed edge k[V₁]→Q₁ is c≫δ₁≫e, where c:k[V₁]→P₁ is the coordinate
inclusion and e:P₀→Q₁ is the base prism. -/
def lastFace : (free.{u, v} k).obj (s.variables 1) ⟶ Q.left.obj (op ⦋1⦌) :=
  coordinate s ≫ P.left.δ (1 : Fin 2) ≫ baseEdge s f g hQ

private theorem faces_compatible : firstFace s g ≫ Q.left.δ (1 : Fin 2) =
    lastFace s f g hQ ≫ Q.left.δ (0 : Fin 2) := by
  simp only [firstFace, lastFace, Category.assoc]
  rw [baseEdge_zero_face]
  have hδ : P.left.δ (1 : Fin 2) ≫ g.left.app (op ⦋0⦌) =
      g.left.app (op ⦋1⦌) ≫ Q.left.δ (1 : Fin 2) :=
    g.left.naturality (SimplexCategory.δ (1 : Fin 2)).op
  exact congrArg (fun z => coordinate s ≫ z) hδ.symm

private theorem firstFace_augmentation : firstFace s g ≫ Q.hom.app (op ⦋1⦌) =
    coordinate s ≫ P.hom.app (op ⦋1⦌) := by
  rw [firstFace, Category.assoc]
  have hε : g.left.app (op ⦋1⦌) ≫ Q.hom.app (op ⦋1⦌) = P.hom.app (op ⦋1⦌) := by
    simpa only [NatTrans.comp_app] using NatTrans.congr_app g.w (op ⦋1⦌)
  exact congrArg (fun z => coordinate s ≫ z) hε

private theorem lastFace_augmentation : lastFace s f g hQ ≫ Q.hom.app (op ⦋1⦌) =
    coordinate s ≫ P.hom.app (op ⦋1⦌) := by
  have hε : P.left.δ (1 : Fin 2) ≫ P.hom.app (op ⦋0⦌) = P.hom.app (op ⦋1⦌) :=
    (P.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op).trans (Category.comp_id _)
  simp only [lastFace, Category.assoc]
  rw [baseEdge_augmentation, hε]

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, prescribe the horn of a two-simplex missing face one: face zero is c≫g₁ and face two is
c≫δ₁≫e. The index j ranges over Fin3 with j≠1. -/
def faces (j : Fin 3) (_hj : j ≠ (1 : Fin 3)) :
    MvPolynomial (s.variables 1) k →ₐ[k] Q.left.obj (op ⦋1⦌) :=
  if j = 0 then (firstFace s g).hom else (lastFace s f g hQ).hom

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, face zero of the first nondegenerate prism horn is c≫g₁:k[V₁]→Q₁. -/
@[simp]
theorem faces_zero : faces s f g hQ 0 (by decide) = (firstFace s g).hom := rfl

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, face two of the first nondegenerate prism horn is c≫δ₁≫e:k[V₁]→Q₁, where e is the base
edge. -/
@[simp]
theorem faces_last : faces s f g hQ 2 (by decide) = (lastFace s f g hQ).hom := rfl

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the exterior horn edges u=c≫g₁ and v=c≫δ₁≫e satisfy u≫δ₁=v≫δ₀. Thus they form a
compatible horn missing face one. -/
theorem compatible : PolynomialHornLift.Compatible k A Q (s.variables 1) 1 1 (faces s f g hQ) := by
  intro j l hj hl hjl
  have hjv : j.val ≠ 1 := by
    intro hjVal
    exact hj (Fin.ext (hjVal.trans (show (1 : Fin 3).val = 1 from rfl).symm))
  have hlv : l.val ≠ 1 := by
    intro hlVal
    exact hl (Fin.ext (hlVal.trans (show (1 : Fin 3).val = 1 from rfl).symm))
  have hjBound : j.val ≤ 2 := Nat.le_of_lt_succ j.isLt
  have hlBound : l.val ≤ 2 := Nat.le_of_lt_succ l.isLt
  have hjlNat : j.val < l.val := hjl
  have hjVal : j.val = 0 := by omega
  have hlVal : l.val = 2 := by omega
  have hjZero : j = 0 := Fin.ext (hjVal.trans (show (0 : Fin 3).val = 0 from rfl).symm)
  have hlTwo : l = 2 := Fin.ext (hlVal.trans (show (2 : Fin 3).val = 2 from rfl).symm)
  subst j
  subst l
  have hpred : (2 : Fin 3).pred (Fin.ne_zero_of_lt hjl) = (1 : Fin 2) := Fin.ext rfl
  have hcast : (0 : Fin 3).castPred (Fin.ne_last_of_lt hjl) = (0 : Fin 2) := Fin.ext rfl
  dsimp only [free]
  simp only [hpred, hcast, faces, ite_eq_left rfl,
    ite_eq_right (by decide : (2 : Fin 3) ≠ 0)]
  exact congrArg CommAlgCat.Hom.hom (faces_compatible s f g hQ)

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, each exterior horn face indexed by j∈Fin3 with j≠1 has augmentation equal to
c≫εP:k[V₁]→A. -/
theorem faces_augmentation (j : Fin 3) (hj : j ≠ (1 : Fin 3)) :
    (Q.hom.app (op ⦋1⦌)).hom.comp (faces s f g hQ j hj) = augmentation s := by
  by_cases h : j = 0
  · subst j
    rw [faces_zero]
    exact congrArg CommAlgCat.Hom.hom (firstFace_augmentation s g)
  · have hface : faces s f g hQ j hj = (lastFace s f g hQ).hom := by
      unfold faces
      exact ite_eq_right h
    rw [hface]
    exact congrArg CommAlgCat.Hom.hom (lastFace_augmentation s f g hQ)

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, fill the compatible inner horn to obtain T:k[V₁]→Q₂. Its zero face is c≫g₁, its final
face is c≫δ₁≫e, and its augmentation is c≫εP. -/
def triangle : (free.{u, v} k).obj (s.variables 1) ⟶ Q.left.obj (op ⦋2⦌) :=
  CommAlgCat.ofHom (PolynomialHornLift.lift k A Q (s.variables 1) 1 1 (augmentation s)
    (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ))

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the first triangle T:k[V₁]→Q₂ satisfies T≫δ₀=c≫g₁. -/
@[reassoc]
theorem triangle_zero_face : triangle s f g hQ ≫ Q.left.δ (0 : Fin 3) = firstFace s g := by
  apply CommAlgCat.hom_ext
  dsimp only [free]
  simp only [triangle, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
  exact (PolynomialHornLift.lift_faces k A Q (s.variables 1) 1 1 (augmentation s)
    (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ) 0 (by decide)).trans
      (faces_zero s f g hQ)

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the first triangle T:k[V₁]→Q₂ satisfies T≫δ₂=c≫δ₁≫e, where e is the base edge. -/
@[reassoc]
theorem triangle_last_face : triangle s f g hQ ≫ Q.left.δ (2 : Fin 3) = lastFace s f g hQ := by
  apply CommAlgCat.hom_ext
  dsimp only [free]
  simp only [triangle, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom]
  exact (PolynomialHornLift.lift_faces k A Q (s.variables 1) 1 1 (augmentation s)
    (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ) 2 (by decide)).trans
      (faces_last s f g hQ)

/-- Let k be a commutative ring, A a commutative k-algebra, P and Q augmented simplicial k-algebras
over A, and s a compatible polynomial splitting of P. Assume that the normalized augmentation of
Q's underlying k-module complex is a quasi-isomorphism. For augmentation-preserving maps
f,g:P→Q, the first triangle T:k[V₁]→Q₂ satisfies T≫εQ=c≫εP. Both sides are k-algebra maps
k[V₁]→A. -/
@[reassoc]
theorem triangle_augmentation : triangle s f g hQ ≫ Q.hom.app (op ⦋2⦌) =
    coordinate s ≫ P.hom.app (op ⦋1⦌) := by
  apply CommAlgCat.hom_ext
  exact PolynomialHornLift.lift_augmentation k A Q (s.variables 1) 1 1 (augmentation s)
    (faces s f g hQ) (compatible s f g hQ) (faces_augmentation s f g hQ)

end CommAlgCat.PolynomialPrismFirstNondegenerateTriangle

end
