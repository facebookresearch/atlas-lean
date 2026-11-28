/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.LinearYonedaCochainPairing
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.ChainMap

/-!
# Alexander–Whitney components selected by a linear-Yoneda pairing

Let C be a preadditive monoidal category with tensor additive in both variables, and X,Y
simplicial objects whose alternating chain complexes have a tensor total. The degree-n
Alexander–Whitney map sums the front/back split over s∈Fin(n+1).

A linear-Yoneda pairing descriptor selecting degrees p,q with p+q=n picks exactly the term
(frontFace X⊗backFace Y) followed by the coefficient maps and their multiplication. The front
face retains vertices 0 through p; the back face retains vertices p through n.
Complementary-degree equality transports keep this formula valid for the presentation q=n−p.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory Simplicial

namespace AlgebraicTopology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ Z : C, ((curriedTensor C).obj Z).Additive]
variable (X Y : SimplicialObject C)
variable [HomologicalComplex.HasTensor
  ((AlgebraicTopology.alternatingFaceMapComplex C).obj X)
  ((AlgebraicTopology.alternatingFaceMapComplex C).obj Y)]
variable {M N P : C}

set_option backward.isDefEq.respectTransparency false in
omit [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive] in
/-- Let C be a category and X a simplicial object. For p,q ∈ ℕ, the front face X_{p+q} → X_p
computed with complement (p+q)−p equals the front face computed with complement q. Both are
induced by the inclusion of the first p+1 vertices. -/
theorem frontFace_add_sub (p q : ℕ) :
    frontFace (C := C) X
        (show p + (p + q - p) = p + q by omega) =
      frontFace (C := C) X (show p + q = p + q by rfl) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.multiGoal false in
omit [MonoidalCategory C] [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive] in
/-- For a simplicial object Y in a preadditive category C and p,q ∈ ℕ, the back face Y_{p+q} →
Y_{(p+q)−p}, followed by the alternating-complex term isomorphism for (p+q)−p=q, equals the
back face Y_{p+q} → Y_q. It retains the last q+1 vertices. -/
theorem backFace_add_sub_comp_XIsoOfEq (p q : ℕ) :
    backFace (C := C) Y
        (show p + (p + q - p) = p + q by omega) ≫
      (((AlgebraicTopology.alternatingFaceMapComplex C).obj Y).XIsoOfEq
        (show p + q - p = q by omega)).hom =
    backFace (C := C) Y (show p + q = p + q by rfl) := by
  change Y.map (backInclusion p (p + q - p) (p + q) (by omega)).op ≫
      eqToHom (congrArg
        (fun n => Y.obj (Opposite.op (SimplexCategory.mk n)))
        (show p + q - p = q by omega)) =
    Y.map (backInclusion p q (p + q) rfl).op
  rw [← eqToHom_map]
  rw [← Y.map_comp]
  apply congrArg Y.map
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  ext i
  · simp [backInclusion, SimplexCategory.δ₀Iter]
  all_goals
    apply congrArg Opposite.op
    apply SimplexCategory.ext
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Let C be preadditive monoidal with tensor additive in both variables, and X,Y simplicial
objects whose alternating chain tensor exists. For μ : M⊗N → P, φ : X_p → M, and ψ : Y_q → N,
the degree-(p+q) Alexander–Whitney component followed by the linear-Yoneda pairing descriptor
equals (frontFace X⊗backFace Y)≫(φ⊗ψ)≫μ. The descriptor selects the tensor-total summand at
(p,q). -/
theorem alternatingComponent_comp_linearYonedaPairingDesc
    (mu : M ⊗ N ⟶ P) (p q : ℕ)
    (phi : X.obj (Opposite.op (SimplexCategory.mk p)) ⟶ M)
    (psi : Y.obj (Opposite.op (SimplexCategory.mk q)) ⟶ N) :
    alternatingComponent X Y (p + q) ≫
        HomologicalComplex.linearYonedaPairingDesc C mu p q phi psi =
      (frontFace (C := C) X rfl ⊗ₘ backFace (C := C) Y rfl) ≫
        (phi ⊗ₘ psi) ≫ mu := by
  unfold HomologicalComplex.linearYonedaPairingDesc
  rw [alternatingComponent_eq_sum, Preadditive.sum_comp]
  rw [Fintype.sum_eq_single (⟨p, by omega⟩ : Fin (p + q + 1))]
  · dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq_of_eq
      (C := C)
      (K₁ := (AlgebraicTopology.alternatingFaceMapComplex C).obj X)
      (K₂ := (AlgebraicTopology.alternatingFaceMapComplex C).obj Y)
      mu p q (p + q) p (p + q - p) rfl (by omega)
      rfl (by omega) phi psi]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    rw [frontFace_add_sub, backFace_add_sub_comp_XIsoOfEq]
    have hfront :
        frontFace (C := C) (p := p) (q := q) (n := p + q) X rfl ≫
            𝟙 (((AlgebraicTopology.alternatingFaceMapComplex C).obj X).X p) =
          frontFace (C := C) (p := p) (q := q) (n := p + q) X rfl :=
      Category.comp_id _
    rw [hfront]
  · intro i hi
    have hne : (i : ℕ) ≠ p := by
      intro h
      apply hi
      apply Fin.ext
      exact h
    dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq]
    simp [hne]

/-- Let C be preadditive monoidal with tensor additive in both variables, X,Y simplicial objects
with alternating chain tensor, n ∈ ℕ, and s∈Fin(n+1). For φ : X_s → M, ψ : Y_{n−s} → N, and μ
: M⊗N → P, the degree-n Alexander–Whitney map followed by the descriptor for s+(n−s)=n equals
the front-face/back-face map followed by φ⊗ψ and μ. It selects the split (s,n−s) with no
additional sign. -/
theorem alternatingComponent_comp_linearYonedaPairingDescOfEq
    (mu : M ⊗ N ⟶ P) (n : ℕ) (s : Fin (n + 1))
    (phi : X.obj (Opposite.op (SimplexCategory.mk s)) ⟶ M)
    (psi : Y.obj (Opposite.op (SimplexCategory.mk (n - s))) ⟶ N) :
    alternatingComponent X Y n ≫
        HomologicalComplex.linearYonedaPairingDescOfEq C mu s (n - s) n
          (by omega) phi psi =
      (frontFace (C := C) X (show s + (n - s) = n by omega) ⊗ₘ
          backFace (C := C) Y (show s + (n - s) = n by omega)) ≫
        (phi ⊗ₘ psi) ≫ mu := by
  rw [alternatingComponent_eq_sum, Preadditive.sum_comp]
  rw [Fintype.sum_eq_single s]
  · dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq
      (C := C)]
    simp
  · intro i hi
    have hne : (i : ℕ) ≠ s := by
      intro h
      apply hi
      apply Fin.ext
      exact h
    dsimp
    simp only [Category.assoc]
    rw [HomologicalComplex.ιTensorObj_comp_linearYonedaPairingDescOfEq
      (C := C)]
    simp [hne]

end AlgebraicTopology.AlexanderWhitney
