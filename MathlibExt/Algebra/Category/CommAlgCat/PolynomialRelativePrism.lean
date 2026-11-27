/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialPrismDegreeAssembly
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy
public import MathlibExt.CategoryTheory.Comma.Over.Diagram
public import Mathlib.Algebra.Homology.Additive

/-!
# Relative homotopies from compatible polynomial splittings

Let k be a commutative ring and P,Q augmented simplicial k-algebras over A. Fix a compatible
polynomial splitting of P, maps f,g:P→Q over A, and a quasi-isomorphism condition on Q's
normalized additive augmentation.

Successive finite prefixes preserve earlier primitive operators and define global maps
Hᵢ:Pₙ→Qₙ₊₁. Their endpoint, exterior-face, common-middle and augmentation identities give a
simplicial homotopy of f and g, including a homotopy of the corresponding diagrams in Over A.

The cotangent functor B→A ↦ A ⊗[B] Ω(B/k), normalized Moore chains and the additive functor M
⊗[A] − transport this homotopy to the induced cotangent and coefficient chain maps. The
ground-ring universe u and algebra parameter v are independent; algebra and cotangent carriers
use max(u,v), while coefficients may have any carrier universe t and tensor output max(t,u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open CategoryTheory.SimplicialObject.SplittingPrismFaceDescent
open CommAlgCat.PolynomialPrismDegreeAssembly
open scoped Simplicial

universe u v t

namespace CommAlgCat.PolynomialRelativePrism

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (f g : P ⟶ Q)
  (hQ : additiveResolutionCondition k A Q)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. Recursively construct a compatible prism prefix through
degree n+1 for each n∈ℕ. Each prefix contains primitive maps and the face and augmentation
identities in its range. -/
def prefixes (s : PolynomialSplitting k P.left) (f g : P ⟶ Q)
    (hQ : additiveResolutionCondition k A Q) : (n : ℕ) → Prefix s f g (n + 1) :=
  Nat.rec (initial s f g hQ) (fun n b => extend s f g n b hQ)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. The prefix at n+1 is the successor extension of the prefix
at n, obtained by adjoining the next nondegenerate degree and its face equations. -/
theorem prefixes_succ (n : ℕ) :
    prefixes s f g hQ (n + 1) = extend s f g n (prefixes s f g hQ n) hQ := rfl

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. If a≤b and m≤a+1, the primitive degree-m prescription in
prefix b equals that in prefix a. -/
theorem prefix_prescribed_le (a b m : ℕ) (hab : a ≤ b) (hm : m ≤ a + 1) :
    (prefixes s f g hQ b).prescribed m = (prefixes s f g hQ a).prescribed m := by
  induction b generalizing a with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases he : a = b + 1
    · subst a
      rfl
    · have hab' : a ≤ b := by omega
      rw [prefixes_succ s f g hQ b,
        extend_prescribed_old s f g b (prefixes s f g hQ b) hQ m (by omega)]
      exact ih a hab' hm

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. Define the global primitive family by taking each degree's
map from the first prefix that contains it. Its degree-m, index-i value has type Nₘ(P)→Qₘ₊₁ for
i≤m. -/
def prescribed : ∀ m : ℕ, Fin (m + 1) → (s.splitting.N m ⟶ Q.left.obj (op ⦋m + 1⦌)) :=
  fun m => match m with
  | 0 => (prefixes s f g hQ 0).prescribed 0
  | m + 1 => (prefixes s f g hQ m).prescribed (m + 1)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. For m≤n+1, the global primitive degree-m family equals the
family stored in prefix n. -/
theorem prescribed_agrees (n m : ℕ) (hm : m ≤ n + 1) :
    prescribed s f g hQ m = (prefixes s f g hQ n).prescribed m := by
  cases m with
  | zero => exact (prefix_prescribed_le s f g hQ 0 n 0 (by omega) (by omega)).symm
  | succ m => exact (prefix_prescribed_le s f g hQ m n (m + 1) (by omega) le_rfl).symm

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. For m≤n+1 and r≤m, coproduct descent of the global
primitive family gives the same whole-degree operator as prefix n. -/
theorem operator_agrees (n m : ℕ) (hm : m ≤ n + 1) (r : ℕ) (hr : r ≤ m) :
    operator s.splitting (prescribed s f g hQ) m r hr =
      operator s.splitting (prefixes s f g hQ n).prescribed m r hr := by
  apply s.splitting.hom_ext'
  intro a
  rw [s.splitting.prismDegree_summand, s.splitting.prismDegree_summand]
  have ha : a.1.unop.len ≤ m := SimplexCategory.len_le_of_epi a.e
  rw [prescribed_agrees s f g hQ n a.1.unop.len (by omega)]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. For every d∈ℕ, the global operators in source degree d+1
satisfy the endpoint, early-face, late-face and common-middle prism identities. -/
def allFaces (d : ℕ) :
    Faces s.splitting (prescribed s f g hQ) f.left g.left d where
  zero := by
    rw [operator_agrees s f g hQ d (d + 1) le_rfl]
    exact ((prefixes s f g hQ d).faces d le_rfl).zero
  last := by
    rw [operator_agrees s f g hQ d (d + 1) le_rfl]
    exact ((prefixes s f g hQ d).faces d le_rfl).last
  early := by
    intro r hr j hj
    rw [operator_agrees s f g hQ d (d + 1) le_rfl,
      operator_agrees s f g hQ d d (by omega)]
    exact ((prefixes s f g hQ d).faces d le_rfl).early r hr j hj
  late := by
    intro r hr j hj hj'
    rw [operator_agrees s f g hQ d (d + 1) le_rfl,
      operator_agrees s f g hQ d d (by omega)]
    exact ((prefixes s f g hQ d).faces d le_rfl).late r hr j hj hj'
  middle := by
    intro r hr
    simp only [operator_agrees s f g hQ d (d + 1) le_rfl]
    exact ((prefixes s f g hQ d).faces d le_rfl).middle r hr

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. The global operator Hᵢ:Pₙ→Qₙ₊₁, for i∈Fin(n+1), is the
splitting-coproduct extension of the global primitive family. It has the prescribed prism faces
and preserves augmentation. -/
def algebraOperator {n : ℕ} (i : Fin (n + 1)) :
    P.left.obj (op ⦋n⦌) ⟶ Q.left.obj (op ⦋n + 1⦌) :=
  s.splitting.prismDegree (prescribed s f g hQ) i

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. In source degree zero, H₀:P₀→Q₁ satisfies H₀≫δ₀=g₀. -/
theorem zero_first : algebraOperator s f g hQ (0 : Fin 1) ≫ Q.left.δ (0 : Fin 2) =
    g.left.app (op ⦋0⦌) := by
  change operator s.splitting (prescribed s f g hQ) 0 0 (by omega) ≫ Q.left.δ 0 = _
  rw [operator_agrees s f g hQ 0 0 (by omega)]
  exact (prefixes s f g hQ 0).zeroFace

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. In source degree zero, H₀:P₀→Q₁ satisfies H₀≫δ₁=f₀. -/
theorem zero_last : algebraOperator s f g hQ (0 : Fin 1) ≫ Q.left.δ (1 : Fin 2) =
    f.left.app (op ⦋0⦌) := by
  change operator s.splitting (prescribed s f g hQ) 0 0 (by omega) ≫ Q.left.δ 1 = _
  rw [operator_agrees s f g hQ 0 0 (by omega)]
  exact (prefixes s f g hQ 0).lastZeroFace

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. For every source degree n and i∈Fin(n+1), Hᵢ≫εQ(n+1)=εP(n). -/
@[reassoc]
theorem algebraOperator_augmentation {n : ℕ} (i : Fin (n + 1)) :
    algebraOperator s f g hQ i ≫ Q.hom.app (op ⦋n + 1⦌) = P.hom.app (op ⦋n⦌) := by
  change operator s.splitting (prescribed s f g hQ) n i.val (by omega) ≫
    Q.hom.app (op ⦋n + 1⦌) = _
  rw [operator_agrees s f g hQ n n (by omega)]
  exact (prefixes s f g hQ n).augmentation n (by omega) i.val (by omega)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. The global operators form a simplicial homotopy between the
underlying algebra maps f and g. Its first endpoint face is g and its last endpoint face is f. -/
def algebraHomotopy : SimplicialObject.Homotopy f.left g.left where
  h i := algebraOperator s f g hQ i
  h_zero_comp_δ_zero n := by
    cases n with
    | zero => exact zero_first s f g hQ
    | succ n => exact (allFaces s f g hQ n).zero
  h_last_comp_δ_last n := by
    cases n with
    | zero => exact zero_last s f g hQ
    | succ n => exact (allFaces s f g hQ n).last
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    have hcast : j.castSucc.val = j.val := rfl
    have hijCast : i.val ≤ j.castSucc.val := hij
    have hijNat : i.val ≤ j.val := hcast ▸ hijCast
    have h := (allFaces s f g hQ n).early (j.val + 1) (by omega) i.val (by omega)
    dsimp only [face, operator] at h
    simp only [Nat.add_sub_cancel] at h
    have hjs : (⟨j.val + 1, by omega⟩ : Fin (n + 2)) = j.succ := Fin.ext rfl
    have hic : (⟨i.val, by omega⟩ : Fin (n + 3)) = i.castSucc := Fin.ext rfl
    have hi : (⟨i.val, by omega⟩ : Fin (n + 2)) = i := Fin.ext rfl
    have hj : (⟨j.val, by omega⟩ : Fin (n + 1)) = j := Fin.ext rfl
    rw [hjs, hic, hi, hj] at h
    exact h
  h_succ_comp_δ_castSucc_succ {n} j :=
    (allFaces s f g hQ n).middle j.val j.is_lt
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    have hcast : j.castSucc.val = j.val := rfl
    have hjiCast : j.castSucc.val < i.val := hji
    have hjiNat : j.val < i.val := hcast ▸ hjiCast
    have h := (allFaces s f g hQ n).late j.val (by omega) (i.val + 1) (by omega) (by omega)
    dsimp only [face, operator] at h
    simp only [Nat.add_sub_cancel] at h
    have hjc : (⟨j.val, by omega⟩ : Fin (n + 2)) = j.castSucc := Fin.ext rfl
    have his : (⟨i.val + 1, by omega⟩ : Fin (n + 3)) = i.succ := Fin.ext rfl
    have hi : (⟨i.val, by omega⟩ : Fin (n + 2)) = i := Fin.ext rfl
    have hj : (⟨j.val, by omega⟩ : Fin (n + 1)) = j := Fin.ext rfl
    rw [hjc, his, hi, hj] at h
    exact h
  h_comp_σ_castSucc_of_le i j hij :=
    (s.splitting.prismDegree_degeneracy_castSucc (prescribed s f g hQ) i j hij).symm
  h_comp_σ_succ_of_lt i j hji :=
    (s.splitting.prismDegree_degeneracy_succ (prescribed s f g hQ) i j hji).symm

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. The same operators, together with their augmentation
equations, form a simplicial homotopy between the induced diagrams of maps in Over A. -/
def homotopy : SimplicialObject.Homotopy (Over.liftDiagramMap A f) (Over.liftDiagramMap A g) where
  h i := Over.homMk (algebraOperator s f g hQ i) (algebraOperator_augmentation s f g hQ i)
  h_zero_comp_δ_zero n := by
    apply Over.OverMorphism.ext
    change algebraOperator s f g hQ (0 : Fin (n + 1)) ≫ Q.left.δ (0 : Fin (n + 2)) =
      g.left.app (op ⦋n⦌)
    exact (algebraHomotopy s f g hQ).h_zero_comp_δ_zero n
  h_last_comp_δ_last n := by
    apply Over.OverMorphism.ext
    change algebraOperator s f g hQ (Fin.last n) ≫ Q.left.δ (Fin.last (n + 1)) =
      f.left.app (op ⦋n⦌)
    exact (algebraHomotopy s f g hQ).h_last_comp_δ_last n
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply Over.OverMorphism.ext
    change algebraOperator s f g hQ j.succ ≫ Q.left.δ i.castSucc =
      P.left.δ i ≫ algebraOperator s f g hQ j
    exact (algebraHomotopy s f g hQ).h_succ_comp_δ_castSucc_of_lt i j hij
  h_succ_comp_δ_castSucc_succ j := by
    apply Over.OverMorphism.ext
    change algebraOperator s f g hQ j.succ ≫ Q.left.δ j.castSucc.succ =
      algebraOperator s f g hQ j.castSucc ≫ Q.left.δ j.castSucc.succ
    exact (algebraHomotopy s f g hQ).h_succ_comp_δ_castSucc_succ j
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply Over.OverMorphism.ext
    change algebraOperator s f g hQ j.castSucc ≫ Q.left.δ i.succ =
      P.left.δ i ≫ algebraOperator s f g hQ j
    exact (algebraHomotopy s f g hQ).h_castSucc_comp_δ_succ_of_lt i j hji
  h_comp_σ_castSucc_of_le i j hij := by
    apply Over.OverMorphism.ext
    change algebraOperator s f g hQ j ≫ Q.left.σ i.castSucc =
      P.left.σ i ≫ algebraOperator s f g hQ j.succ
    exact (algebraHomotopy s f g hQ).h_comp_σ_castSucc_of_le i j hij
  h_comp_σ_succ_of_lt i j hji := by
    apply Over.OverMorphism.ext
    change algebraOperator s f g hQ j ≫ Q.left.σ i.succ =
      P.left.σ i ≫ algebraOperator s f g hQ j.castSucc
    exact (algebraHomotopy s f g hQ).h_comp_σ_succ_of_lt i j hji

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. Apply the functor B→A ↦ A ⊗[B] Ω(B/k) to the
augmentation-slice homotopy. This gives a simplicial homotopy between the cotangent maps induced
by f and g. -/
def cotangentHomotopy : SimplicialObject.Homotopy
    (cotangentSimplicialMap k A f) (cotangentSimplicialMap k A g) :=
  (homotopy s f g hQ).whiskerRight (cotangentFunctor k A)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. Normalized Moore chains send the cotangent simplicial
homotopy to a chain homotopy between the normalized cotangent maps induced by f and g. -/
def normalizedCotangentHomotopy : _root_.Homotopy
    ((normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A f))
    ((normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A g)) :=
  SimplicialObject.Homotopy.toNormalizedChainHomotopy (cotangentHomotopy s f g hQ)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and f,g:P→Q maps over A. Assume that Q's normalized additive
augmentation is a quasi-isomorphism. For any A-module M in an independent carrier universe t,
the additive functor M ⊗[A] − transports this chain homotopy to the coefficient-tensored
normalized cotangent maps. The tensor carrier is max(t,u,v), where u is the ground-ring universe
and max(u,v) the algebra carrier. -/
def coefficientHomotopy (M : ModuleCat.{t} A) : _root_.Homotopy
    ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map ((normalizedMooreComplex (ModuleCat.{max u v} A)).map
        (cotangentSimplicialMap k A f)))
    ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map ((normalizedMooreComplex (ModuleCat.{max u v} A)).map
        (cotangentSimplicialMap k A g))) :=
  ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomotopy
    (normalizedCotangentHomotopy s f g hQ)

end CommAlgCat.PolynomialRelativePrism

end
