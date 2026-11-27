/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitTruncatedComparison

/-!
# Comparison maps from polynomial-split simplicial algebras

Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and s a compatible
polynomial splitting of P. Suppose that Q's normalized additive augmentation is a
quasi-isomorphism.

Surjectivity of Q₀→A permits a polynomial lift on the degree-zero generators.
Splitting-coproduct descent gives the first comparison component. Successive polynomial boundary
lifts extend every truncated comparison while preserving its lower components. The resulting
components are natural for all simplex-category morphisms and form an augmented map P→Q.

The ground-ring universe u and algebra parameter v are independent. The source, target and
polynomial variable sets lie in the stable algebra carrier universe max(u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialSplitComparison

open PolynomialSplitDegreeExtension

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (hQ : additiveResolutionCondition k A Q)

include hQ in
/-- Let k be a commutative ring and Q an augmented simplicial k-algebra over A whose normalized
additive augmentation is a quasi-isomorphism. Its degree-zero augmentation εQ₀:Q₀→A is
surjective. -/
theorem augmentation_surjective : Function.Surjective (Q.hom.app (op ⦋0⦌)).hom := by
  let X := additiveAugmentedResolution k A Q
  let _ : QuasiIso (ModuleResolutionAsphericity.augmentation X) := hQ
  exact ModuleResolutionAsphericity.original_augmentation_zero_surjective_of_quasiIso X

/-- For a compatible polynomial splitting of an augmented simplicial k-algebra P over A, the
polynomial augmentation k[V₀]→A is the degree-zero polynomial coordinate inclusion followed by
εP₀. -/
def zeroAugmentation : MvPolynomial (s.variables 0) k →ₐ[k] A :=
  ((s.polynomialIso 0).inv ≫ s.splitting.ι 0 ≫ P.hom.app (op ⦋0⦌)).hom

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. Choose a lift in Q₀ of the augmentation of every degree-zero polynomial
generator. Polynomial evaluation gives N₀(P)→Q₀ with the prescribed augmentation. -/
def zeroNondegenerateMap : s.splitting.N 0 ⟶ Q.left.obj (op ⦋0⦌) :=
  (s.polynomialIso 0).hom ≫ CommAlgCat.ofHom (MvPolynomial.aeval
    (fun x => Classical.choose (augmentation_surjective hQ (zeroAugmentation s (MvPolynomial.X x)))))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. The chosen nondegenerate map u:N₀(P)→Q₀ satisfies u≫εQ₀=ι₀≫εP₀, where
ι₀:N₀(P)→P₀ is the summand inclusion. -/
theorem zeroNondegenerateMap_augmentation :
    zeroNondegenerateMap s hQ ≫ Q.hom.app (op ⦋0⦌) = s.splitting.ι 0 ≫ P.hom.app (op ⦋0⦌) := by
  have h : CommAlgCat.ofHom (MvPolynomial.aeval
      (fun x => Classical.choose (augmentation_surjective hQ (zeroAugmentation s (MvPolynomial.X x))))) ≫
      Q.hom.app (op ⦋0⦌) = (s.polynomialIso 0).inv ≫ s.splitting.ι 0 ≫ P.hom.app (op ⦋0⦌) := by
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro x
    change (Q.hom.app (op ⦋0⦌)).hom
        (MvPolynomial.aeval (fun x => Classical.choose
          (augmentation_surjective hQ (zeroAugmentation s (MvPolynomial.X x)))) (MvPolynomial.X x)) =
      zeroAugmentation s (MvPolynomial.X x)
    rw [MvPolynomial.aeval_X]
    exact Classical.choose_spec (augmentation_surjective hQ (zeroAugmentation s (MvPolynomial.X x)))
  rw [zeroNondegenerateMap, Category.assoc, h]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The splitting index set in simplicial degree zero has only the identity index: every
epimorphism-indexed summand comes from degree zero and the identity of the zero simplex. -/
theorem zero_index_identity (a : SimplicialObject.Splitting.IndexSet (op ⦋0⦌)) :
    a = SimplicialObject.Splitting.IndexSet.id _ :=
  (a.eqId_iff_len_le).mpr (Nat.zero_le _)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. The map on any degree-zero splitting summand is the chosen map N₀(P)→Q₀,
transported along the unique identity-index identification. -/
def zeroSummandMap (a : SimplicialObject.Splitting.IndexSet (op ⦋0⦌)) :
    s.splitting.N a.1.unop.len ⟶ Q.left.obj (op ⦋0⦌) :=
  eqToHom (congrArg (fun b => s.splitting.N b.1.unop.len) (zero_index_identity a)) ≫
    zeroNondegenerateMap s hQ

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. Descend the degree-zero summand maps through the splitting coproduct to
obtain a whole algebra map P₀→Q₀. -/
def zeroMap : P.left.obj (op ⦋0⦌) ⟶ Q.left.obj (op ⦋0⦌) :=
  s.splitting.desc (op ⦋0⦌) (zeroSummandMap s hQ)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. Restricting the whole degree-zero comparison along ι₀:N₀(P)→P₀ recovers the
chosen nondegenerate map. -/
theorem zeroMap_distinguished : s.splitting.ι 0 ≫ zeroMap s hQ = zeroNondegenerateMap s hQ := by
  have h := s.splitting.ι_desc (op ⦋0⦌) (zeroSummandMap s hQ) (SimplicialObject.Splitting.IndexSet.id _)
  have hc : s.splitting.ι 0 ≫ zeroMap s hQ = zeroSummandMap s hQ (SimplicialObject.Splitting.IndexSet.id _) := by
    change s.splitting.ι 0 ≫ s.splitting.desc (op ⦋0⦌) (zeroSummandMap s hQ) = _
    have hi := SimplicialObject.Splitting.cofan_inj_id s.splitting 0
    exact (congrArg (fun i => i ≫ s.splitting.desc (op ⦋0⦌) (zeroSummandMap s hQ)) hi).symm.trans h
  have hz : zeroSummandMap s hQ (SimplicialObject.Splitting.IndexSet.id _) = zeroNondegenerateMap s hQ :=
    Category.id_comp _
  exact hc.trans hz

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. The whole comparison u₀:P₀→Q₀ satisfies u₀≫εQ₀=εP₀. -/
theorem zeroMap_augmentation : zeroMap s hQ ≫ Q.hom.app (op ⦋0⦌) = P.hom.app (op ⦋0⦌) := by
  apply s.splitting.hom_ext'
  intro a
  obtain rfl := zero_index_identity a
  have hi := SimplicialObject.Splitting.cofan_inj_id s.splitting 0
  have h : s.splitting.ι 0 ≫ (zeroMap s hQ ≫ Q.hom.app (op ⦋0⦌)) =
      s.splitting.ι 0 ≫ P.hom.app (op ⦋0⦌) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ Q.hom.app (op ⦋0⦌)) (zeroMap_distinguished s hQ)).trans
        (zeroNondegenerateMap_augmentation s hQ))
  exact (congrArg (fun i => i ≫ (zeroMap s hQ ≫ Q.hom.app (op ⦋0⦌))) hi).trans
    (h.trans (congrArg (fun i => i ≫ P.hom.app (op ⦋0⦌)) hi.symm))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. The degree-zero comparison over A defines an augmented comparison truncated
through simplicial degree zero. -/
def initialComparison : TruncatedComparison k A P Q 0 :=
  PolynomialSplitTruncatedComparison.ofZero
    (Over.homMk (zeroMap s hQ) (zeroMap_augmentation s hQ))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. Starting with the degree-zero comparison, recursively extend to an augmented
comparison through every natural-number degree n. -/
def stages : (n : ℕ) → TruncatedComparison k A P Q n :=
  Nat.rec (initialComparison s hQ)
    (fun n H => PolynomialSplitTruncatedComparison.extend s n H hQ)

private theorem stages_restrict (n : ℕ) :
    (Over.post (SimplicialObject.Truncated.trunc (CommAlgCat.{max u v} k) (n + 1) n)).map
      (stages s hQ (n + 1)) = stages s hQ n :=
  PolynomialSplitTruncatedComparison.extend_restrict s n (stages s hQ n) hQ

private theorem stages_component_succ (n m : ℕ) (hm : m ≤ n) :
    component (n + 1) (stages s hQ (n + 1)) m (hm.trans (Nat.le_succ n)) =
      component n (stages s hQ n) m hm :=
  congrArg (fun f => f.left.app (op ⟨⦋m⦌, hm⟩)) (stages_restrict s hQ n)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. The component uₘ:Pₘ→Qₘ is the degree-m component of the constructed
comparison truncated through m. -/
def comparisonComponent (m : ℕ) : P.left.obj (op ⦋m⦌) ⟶ Q.left.obj (op ⦋m⦌) :=
  component m (stages s hQ m) m le_rfl

private theorem stages_component (n m : ℕ) (hm : m ≤ n) :
    component n (stages s hQ n) m hm = comparisonComponent s hQ m := by
  induction n generalizing m with
  | zero =>
      obtain rfl := Nat.eq_zero_of_le_zero hm
      rfl
  | succ n ih =>
      by_cases he : m = n + 1
      · subst m
        rfl
      · have hm' : m ≤ n := by omega
        rw [stages_component_succ s hQ n m hm']
        exact ih m hm'

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. For every simplex morphism θ:op[m]→op[l], P(θ)≫uₗ=uₘ≫Q(θ), where u denotes
the constructed comparison components. -/
@[reassoc]
theorem comparisonComponent_naturality {m l : ℕ} (θ : op ⦋m⦌ ⟶ op ⦋l⦌) :
    P.left.map θ ≫ comparisonComponent s hQ l = comparisonComponent s hQ m ≫ Q.left.map θ := by
  let N := max m l
  have hm : m ≤ N := le_max_left _ _
  have hl : l ≤ N := le_max_right _ _
  have h := component_naturality N (stages s hQ N) hm hl θ
  rw [stages_component s hQ N l hl, stages_component s hQ N m hm] at h
  exact h

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. The constructed degree components and their naturality form an augmented
simplicial k-algebra morphism u:P→Q over A. -/
def comparison : P ⟶ Q :=
  Over.homMk
    { app Δ := comparisonComponent s hQ Δ.unop.len
      naturality {Δ Δ'} θ := comparisonComponent_naturality s hQ θ }
    (by
      apply NatTrans.ext
      funext Δ
      exact component_augmentation Δ.unop.len (stages s hQ Δ.unop.len) Δ.unop.len le_rfl)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. The degree-m component of the global comparison u:P→Q is exactly the map
constructed from its finite stage m. -/
@[simp]
theorem comparison_app (m : ℕ) :
    (comparison s hQ).left.app (op ⦋m⦌) = comparisonComponent s hQ m := rfl

include s hQ in
/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, and assume that Q's normalized additive augmentation is a
quasi-isomorphism. There exists an augmentation-preserving simplicial k-algebra map P→Q. -/
theorem exists_comparison : Nonempty (P ⟶ Q) := ⟨comparison s hQ⟩

end CommAlgCat.PolynomialSplitComparison

end
