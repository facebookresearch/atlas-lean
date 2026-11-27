/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitting
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialBoundaryComparison
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-!
# Successor degree of a polynomial-split comparison

Let k be a commutative ring and P,Q augmented simplicial k-algebras over A. Fix a compatible
polynomial splitting of P and an augmented comparison H restricted to simplicial degrees at most
n. Assume that Q's normalized additive augmentation is a quasi-isomorphism.

On the new nondegenerate summand in degree n+1, the prescribed boundary is the source face
followed by Hₙ. A polynomial boundary filler gives its new map. The splitting coproduct combines
this map with the lower comparison maps on every proper degenerate summand. The whole degree-n+1
comparison commutes with all faces, incoming degeneracies and augmentation.

All n∈ℕ, including zero, are allowed. Ground-ring and algebra carrier parameters remain
independent, with algebra and polynomial variable carriers at max(u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialSplitDegreeExtension

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)
  (P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))

/-- For augmented simplicial k-algebras P,Q over A and n∈ℕ, a truncated comparison is a morphism
over A after restricting both diagrams to simplices of dimension at most n. -/
abbrev TruncatedComparison (n : ℕ) :=
  ((Over.post (SimplicialObject.truncation n)).obj P) ⟶
    ((Over.post (SimplicialObject.truncation n)).obj Q)

variable {k A P Q}
  (s : PolynomialSplitting k P.left) (n : ℕ)
  (H : TruncatedComparison k A P Q n)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. For m≤n, its component Hₘ is the k-algebra
map Pₘ→Qₘ in that source degree. -/
def component (m : ℕ) (hm : m ≤ n) : P.left.obj (op ⦋m⦌) ⟶ Q.left.obj (op ⦋m⦌) :=
  H.left.app (op ⟨⦋m⦌, hm⟩)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. For m,l≤n and every θ:op[m]→op[l], the
component maps satisfy P(θ)≫Hₗ=Hₘ≫Q(θ). -/
@[reassoc]
theorem component_naturality {m l : ℕ} (hm : m ≤ n) (hl : l ≤ n)
    (θ : op ⦋m⦌ ⟶ op ⦋l⦌) :
    P.left.map θ ≫ component n H l hl = component n H m hm ≫ Q.left.map θ := by
  have h := H.left.naturality (SimplexCategory.Truncated.Hom.tr θ.unop hl hm).op
  have hP : ((Over.post (SimplicialObject.truncation n)).obj P).left.map
      (SimplexCategory.Truncated.Hom.tr θ.unop hl hm).op = P.left.map θ := by
    change P.left.map θ.unop.op = P.left.map θ
    rw [Quiver.Hom.op_unop]
  have hQ : ((Over.post (SimplicialObject.truncation n)).obj Q).left.map
      (SimplexCategory.Truncated.Hom.tr θ.unop hl hm).op = Q.left.map θ := by
    change Q.left.map θ.unop.op = Q.left.map θ
    rw [Quiver.Hom.op_unop]
  exact (congrArg (fun f => f ≫ component n H l hl) hP.symm).trans
    (h.trans (congrArg (fun f => component n H m hm ≫ f) hQ))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. For m≤n, the lower component satisfies
Hₘ≫εQₘ=εPₘ. -/
@[reassoc]
theorem component_augmentation (m : ℕ) (hm : m ≤ n) :
    component n H m hm ≫ Q.hom.app (op ⦋m⦌) = P.hom.app (op ⦋m⦌) :=
  NatTrans.congr_app H.w (op ⟨⦋m⦌, hm⟩)

/-- For a commutative ring k and an augmented simplicial k-algebra P over A with compatible
polynomial splitting s, the new coordinate inclusion c:k[V(n+1)]→P(n+1) is the inverse
polynomial presentation of N(n+1)(P) followed by its summand inclusion. -/
def coordinateInclusion :
    CommAlgCat.of k (MvPolynomial (s.variables (n + 1)) k) ⟶ P.left.obj (op ⦋n + 1⦌) :=
  (s.polynomialIso (n + 1)).inv ≫ s.splitting.ι (n + 1)

/-- For a commutative ring k and an augmented simplicial k-algebra P over A with compatible
polynomial splitting s, the augmentation on the successor variables is α=c≫εP(n+1):k[V(n+1)]→A. -/
def generatorAugmentation : MvPolynomial (s.variables (n + 1)) k →ₐ[k] A :=
  (coordinateInclusion s n ≫ P.hom.app (op ⦋n + 1⦌)).hom

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Prescribe the new polynomial boundary by uⱼ=c≫δj≫Hₙ:k[V(n+1)]→Qₙ for j∈Fin(n+2). -/
def generatorFaces (j : Fin (n + 2)) :
    MvPolynomial (s.variables (n + 1)) k →ₐ[k] Q.left.obj (op ⦋n⦌) :=
  (coordinateInclusion s n ≫ P.left.δ j ≫ component n H n le_rfl).hom

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
The prescribed maps uⱼ=c≫δj≫Hₙ satisfy uⱼ≫δ(l−1)=uₗ≫δj for j<l in Fin(n+2). -/
theorem generatorFaces_compatible :
    PolynomialBoundaryComparison.BoundaryCompatible k A Q (s.variables (n + 1)) n
      (generatorFaces s n H) := by
  cases n with
  | zero => trivial
  | succ n =>
      intro i j hij
      have hδ :
          P.left.δ i ≫ P.left.δ (j.pred (Fin.ne_zero_of_lt hij)) =
            P.left.δ j ≫ P.left.δ (i.castPred (Fin.ne_last_of_lt hij)) := by
        have h := P.left.δ_comp_δ' (i := i.castPred (Fin.ne_last_of_lt hij)) (j := j)
          (by simpa only [Fin.castSucc_castPred] using hij)
        simpa only [Fin.castSucc_castPred] using h.symm
      have hj := component_naturality (n + 1) H le_rfl (Nat.le_succ n)
        (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))).op
      have hi := component_naturality (n + 1) H le_rfl (Nat.le_succ n)
        (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))).op
      have h :
          (coordinateInclusion s (n + 1) ≫ P.left.δ i ≫ component (n + 1) H (n + 1) le_rfl) ≫
              Q.left.δ (j.pred (Fin.ne_zero_of_lt hij)) =
            (coordinateInclusion s (n + 1) ≫ P.left.δ j ≫ component (n + 1) H (n + 1) le_rfl) ≫
              Q.left.δ (i.castPred (Fin.ne_last_of_lt hij)) := by
        simp only [Category.assoc]
        change coordinateInclusion s (n + 1) ≫ P.left.δ i ≫
          component (n + 1) H (n + 1) le_rfl ≫
            Q.left.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt hij))).op =
          coordinateInclusion s (n + 1) ≫ P.left.δ j ≫
            component (n + 1) H (n + 1) le_rfl ≫
              Q.left.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt hij))).op
        rw [← hj, ← hi]
        change coordinateInclusion s (n + 1) ≫ P.left.δ i ≫
          P.left.δ (j.pred (Fin.ne_zero_of_lt hij)) ≫ component (n + 1) H n (Nat.le_succ n) =
          coordinateInclusion s (n + 1) ≫ P.left.δ j ≫
            P.left.δ (i.castPred (Fin.ne_last_of_lt hij)) ≫ component (n + 1) H n (Nat.le_succ n)
        rw [← Category.assoc (P.left.δ i)
          (P.left.δ (j.pred (Fin.ne_zero_of_lt hij))) (component (n + 1) H n (Nat.le_succ n)),
          ← Category.assoc (P.left.δ j)
          (P.left.δ (i.castPred (Fin.ne_last_of_lt hij))) (component (n + 1) H n (Nat.le_succ n)), hδ]
      exact congrArg CommAlgCat.Hom.hom h

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Every prescribed face uⱼ has uⱼ≫εQₙ=α, where α=c≫εP(n+1) is the successor coordinate
augmentation. -/
theorem generatorFaces_augmentation (j : Fin (n + 2)) :
    (Q.hom.app (op ⦋n⦌)).hom.comp (generatorFaces s n H j) = generatorAugmentation s n := by
  have hε : P.left.δ j ≫ P.hom.app (op ⦋n⦌) = P.hom.app (op ⦋n + 1⦌) :=
    (P.hom.naturality (SimplexCategory.δ j).op).trans (Category.comp_id _)
  have h : (coordinateInclusion s n ≫ P.left.δ j ≫ component n H n le_rfl) ≫
      Q.hom.app (op ⦋n⦌) = coordinateInclusion s n ≫ P.hom.app (op ⦋n + 1⦌) := by
    simp only [Category.assoc]
    rw [component_augmentation, hε]
  exact congrArg CommAlgCat.Hom.hom h

variable (hQ : additiveResolutionCondition k A Q)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. Fill the prescribed
polynomial boundary to obtain v:N(n+1)(P)→Q(n+1), preserving all its faces and augmentation. -/
def nondegenerateMap : s.splitting.N (n + 1) ⟶ Q.left.obj (op ⦋n + 1⦌) :=
  (s.polynomialIso (n + 1)).hom ≫ CommAlgCat.ofHom
    (PolynomialBoundaryComparison.boundaryLift k A Q (s.variables (n + 1)) hQ n
      (generatorAugmentation s n) (generatorFaces s n H)
      (generatorFaces_compatible s n H) (generatorFaces_augmentation s n H))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. For every j∈Fin(n+2),
v≫δj=ι(n+1)≫δj≫Hₙ, where v is the new nondegenerate map and ι its source summand inclusion. -/
@[reassoc]
theorem nondegenerateMap_faces (j : Fin (n + 2)) :
    nondegenerateMap s n H hQ ≫ Q.left.δ j =
      s.splitting.ι (n + 1) ≫ P.left.δ j ≫ component n H n le_rfl := by
  have h : CommAlgCat.ofHom
      (PolynomialBoundaryComparison.boundaryLift k A Q (s.variables (n + 1)) hQ n
        (generatorAugmentation s n) (generatorFaces s n H)
        (generatorFaces_compatible s n H) (generatorFaces_augmentation s n H)) ≫ Q.left.δ j =
      coordinateInclusion s n ≫ P.left.δ j ≫ component n H n le_rfl := by
    apply CommAlgCat.hom_ext
    exact PolynomialBoundaryComparison.boundaryLift_faces k A Q (s.variables (n + 1)) hQ n
      (generatorAugmentation s n) (generatorFaces s n H)
      (generatorFaces_compatible s n H) (generatorFaces_augmentation s n H) j
  rw [nondegenerateMap, Category.assoc, h, coordinateInclusion]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. The nondegenerate lift
satisfies v≫εQ(n+1)=ι(n+1)≫εP(n+1). -/
@[reassoc]
theorem nondegenerateMap_augmentation :
    nondegenerateMap s n H hQ ≫ Q.hom.app (op ⦋n + 1⦌) =
      s.splitting.ι (n + 1) ≫ P.hom.app (op ⦋n + 1⦌) := by
  have h : CommAlgCat.ofHom
      (PolynomialBoundaryComparison.boundaryLift k A Q (s.variables (n + 1)) hQ n
        (generatorAugmentation s n) (generatorFaces s n H)
        (generatorFaces_compatible s n H) (generatorFaces_augmentation s n H)) ≫ Q.hom.app (op ⦋n + 1⦌) =
      coordinateInclusion s n ≫ P.hom.app (op ⦋n + 1⦌) := by
    apply CommAlgCat.hom_ext
    exact PolynomialBoundaryComparison.boundaryLift_augmentation k A Q (s.variables (n + 1)) hQ n
      (generatorAugmentation s n) (generatorFaces s n H)
      (generatorFaces_compatible s n H) (generatorFaces_augmentation s n H)
  rw [nondegenerateMap, Category.assoc, h, coordinateInclusion]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- A nonidentity splitting index in degree n+1 is given by an epimorphism from the (n+1)-simplex to
a simplex of degree at most n. -/
theorem lower_dimension
    (a : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌)) (ha : ¬ a.EqId) :
    a.1.unop.len ≤ n :=
  Nat.lt_succ_iff.mp (Nat.lt_of_not_ge ((a.eqId_iff_len_le).not.mp ha))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. On the identity-index
summand use the new nondegenerate lift. On a proper index from degree m≤n, use ιₘ≫Hₘ followed by
the Q-map of its indexing degeneracy. -/
def summandMap (a : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌)) :
    s.splitting.N a.1.unop.len ⟶ Q.left.obj (op ⦋n + 1⦌) := by
  classical
  exact if ha : a.EqId then
    eqToHom (congrArg s.splitting.N ((a.eqId_iff_len_eq).mp ha)) ≫ nondegenerateMap s n H hQ
  else
    s.splitting.ι a.1.unop.len ≫ component n H a.1.unop.len (lower_dimension n a ha) ≫ Q.left.map a.e.op

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. The splitting coproduct
extends all successor-degree summand prescriptions to a whole map vₙ₊₁:P(n+1)→Q(n+1). -/
def degreeMap : P.left.obj (op ⦋n + 1⦌) ⟶ Q.left.obj (op ⦋n + 1⦌) :=
  s.splitting.desc (op ⦋n + 1⦌) (summandMap s n H hQ)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. Restricting vₙ₊₁ along
any splitting cofan injection returns the prescription on that summand. -/
@[reassoc]
theorem degreeMap_summand (a : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌)) :
    (s.splitting.cofan (op ⦋n + 1⦌)).inj a ≫ degreeMap s n H hQ = summandMap s n H hQ a :=
  s.splitting.ι_desc _ _ a

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. Restriction along
ι(n+1):N(n+1)(P)→P(n+1) returns the new nondegenerate boundary lift. -/
@[reassoc]
theorem degreeMap_distinguished :
    s.splitting.ι (n + 1) ≫ degreeMap s n H hQ = nondegenerateMap s n H hQ := by
  let a := SimplicialObject.Splitting.IndexSet.id (op ⦋n + 1⦌)
  have h := degreeMap_summand s n H hQ a
  have hs : summandMap s n H hQ a = nondegenerateMap s n H hQ := by
    dsimp only [summandMap]
    exact (dite_eq_left (show a.EqId from rfl)).trans (Category.id_comp _)
  exact (congrArg (fun f => f ≫ degreeMap s n H hQ)
    (s.splitting.cofan_inj_id (n + 1)).symm).trans (h.trans hs)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. On a proper splitting
index of degree m≤n, the whole successor map restricts to ιₘ≫Hₘ≫Q(e.op), where e is the indexing
epimorphism. -/
@[reassoc]
theorem degreeMap_lower (a : SimplicialObject.Splitting.IndexSet (op ⦋n + 1⦌))
    (ha : ¬ a.EqId) (hd : a.1.unop.len ≤ n) :
    (s.splitting.cofan (op ⦋n + 1⦌)).inj a ≫ degreeMap s n H hQ =
      s.splitting.ι a.1.unop.len ≫ component n H a.1.unop.len hd ≫ Q.left.map a.e.op := by
  rw [degreeMap_summand, summandMap, dif_neg ha]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. For j∈Fin(n+2),
vₙ₊₁≫δj=δj≫Hₙ. -/
@[reassoc]
theorem degreeMap_faces (j : Fin (n + 2)) :
    degreeMap s n H hQ ≫ Q.left.δ j = P.left.δ j ≫ component n H n le_rfl := by
  apply s.splitting.hom_ext'
  intro a
  by_cases ha : a.EqId
  · change a = SimplicialObject.Splitting.IndexSet.id _ at ha
    subst a
    erw [SimplicialObject.Splitting.cofan_inj_id, ← Category.assoc,
      degreeMap_distinguished, nondegenerateMap_faces]
    rfl
  · let hd := lower_dimension n a ha
    let ι := s.splitting.ι a.1.unop.len
    let c := component n H a.1.unop.len hd
    let θ := (SimplexCategory.δ j).op
    let δP := P.left.map θ
    let δQ := Q.left.map θ
    let p := P.left.map a.e.op
    let q := Q.left.map a.e.op
    let f := component n H n le_rfl
    have hι := s.splitting.cofan_inj_eq a
    have hlow := degreeMap_lower s n H hQ a ha hd
    have hθ := component_naturality n H hd le_rfl (a.e.op ≫ θ)
    have hfirst := (Category.assoc ((s.splitting.cofan (op ⦋n + 1⦌)).inj a)
      (degreeMap s n H hQ) δQ).symm.trans (congrArg (fun z => z ≫ δQ) hlow)
    have hmap : (ι ≫ (c ≫ q)) ≫ δQ = ι ≫ (c ≫ Q.left.map (a.e.op ≫ θ)) :=
      (Category.assoc ι (c ≫ q) δQ).trans
        (congrArg (fun z => ι ≫ z) ((Category.assoc c q δQ).trans
          (congrArg (fun z => c ≫ z) (Q.left.map_comp a.e.op θ).symm)))
    have hlast : ι ≫ (P.left.map (a.e.op ≫ θ) ≫ f) =
        (s.splitting.cofan (op ⦋n + 1⦌)).inj a ≫ (δP ≫ f) :=
      (congrArg (fun z => ι ≫ (z ≫ f)) (P.left.map_comp a.e.op θ)).trans
        ((congrArg (fun z => ι ≫ z) (Category.assoc p δP f)).trans
          ((Category.assoc ι p (δP ≫ f)).symm.trans
            (congrArg (fun z => z ≫ (δP ≫ f)) hι.symm)))
    exact hfirst.trans (hmap.trans ((congrArg (fun z => ι ≫ z) hθ.symm).trans hlast))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. The whole successor map
satisfies vₙ₊₁≫εQ(n+1)=εP(n+1). -/
@[reassoc]
theorem degreeMap_augmentation :
    degreeMap s n H hQ ≫ Q.hom.app (op ⦋n + 1⦌) = P.hom.app (op ⦋n + 1⦌) := by
  apply s.splitting.hom_ext'
  intro a
  by_cases ha : a.EqId
  · change a = SimplicialObject.Splitting.IndexSet.id _ at ha
    subst a
    erw [SimplicialObject.Splitting.cofan_inj_id, ← Category.assoc,
      degreeMap_distinguished, nondegenerateMap_augmentation]
    rfl
  · let hd := lower_dimension n a ha
    let ι := s.splitting.ι a.1.unop.len
    let c := component n H a.1.unop.len hd
    let p := P.left.map a.e.op
    let q := Q.left.map a.e.op
    let εP := P.hom.app (op ⦋n + 1⦌)
    let εQ := Q.hom.app (op ⦋n + 1⦌)
    have hι := s.splitting.cofan_inj_eq a
    have hlow := degreeMap_lower s n H hQ a ha hd
    have hQε : q ≫ εQ = Q.hom.app a.1 :=
      (Q.hom.naturality a.e.op).trans (Category.comp_id _)
    have hPε : p ≫ εP = P.hom.app a.1 :=
      (P.hom.naturality a.e.op).trans (Category.comp_id _)
    have hc : c ≫ Q.hom.app a.1 = P.hom.app a.1 :=
      component_augmentation n H a.1.unop.len hd
    have hfirst := (Category.assoc ((s.splitting.cofan (op ⦋n + 1⦌)).inj a)
      (degreeMap s n H hQ) εQ).symm.trans (congrArg (fun z => z ≫ εQ) hlow)
    have hmap : (ι ≫ (c ≫ q)) ≫ εQ = ι ≫ P.hom.app a.1 :=
      (Category.assoc ι (c ≫ q) εQ).trans
        (congrArg (fun z => ι ≫ z) ((Category.assoc c q εQ).trans
          ((congrArg (fun z => c ≫ z) hQε).trans hc)))
    have hlast : ι ≫ P.hom.app a.1 = (s.splitting.cofan (op ⦋n + 1⦌)).inj a ≫ εP :=
      (congrArg (fun z => ι ≫ z) hPε.symm).trans
        ((Category.assoc ι p εP).symm.trans (congrArg (fun z => z ≫ εP) hι.symm))
    exact hfirst.trans (hmap.trans hlast)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, n∈ℕ, and H a comparison
over A restricted to simplicial degrees at most n. Fix a compatible polynomial splitting s of P.
Assume that Q's normalized additive augmentation is a quasi-isomorphism. For m≤n and
θ:op[m]→op[n+1] whose opposite is epi, P(θ)≫vₙ₊₁=Hₘ≫Q(θ). -/
@[reassoc]
theorem degreeMap_epi_naturality (m : ℕ) (hm : m ≤ n)
    (θ : op ⦋m⦌ ⟶ op ⦋n + 1⦌) [Epi θ.unop] :
    P.left.map θ ≫ degreeMap s n H hQ = component n H m hm ≫ Q.left.map θ := by
  apply s.splitting.hom_ext'
  intro a
  have hd : a.1.unop.len ≤ n := (SimplexCategory.len_le_of_epi a.e).trans hm
  have ha : ¬ (a.epiComp θ).EqId := by
    intro h
    have he := ((a.epiComp θ).eqId_iff_len_eq).mp h
    change a.1.unop.len = n + 1 at he
    omega
  let ι := s.splitting.ι a.1.unop.len
  let c := component n H a.1.unop.len hd
  let f := component n H m hm
  let p := P.left.map a.e.op
  let q := Q.left.map a.e.op
  let t := Q.left.map θ
  have hι := s.splitting.cofan_inj_eq a
  have hθ := component_naturality n H hd hm a.e.op
  have hlow := degreeMap_lower s n H hQ (a.epiComp θ) ha hd
  have hepi := s.splitting.cofan_inj_epi_naturality a θ
  have hfirst := (Category.assoc ((s.splitting.cofan (op ⦋m⦌)).inj a)
    (P.left.map θ) (degreeMap s n H hQ)).symm.trans
      ((congrArg (fun z => z ≫ degreeMap s n H hQ) hepi).trans hlow)
  have hmap : Q.left.map (a.epiComp θ).e.op = q ≫ t := by
    change Q.left.map (θ.unop ≫ a.e).op = _
    rw [op_comp, Quiver.Hom.op_unop]
    exact Q.left.map_comp _ _
  have hmiddle : ι ≫ (c ≫ Q.left.map (a.epiComp θ).e.op) = ι ≫ ((p ≫ f) ≫ t) :=
    (congrArg (fun z => ι ≫ (c ≫ z)) hmap).trans
      ((congrArg (fun z => ι ≫ z) (Category.assoc c q t).symm).trans
        (congrArg (fun z => ι ≫ (z ≫ t)) hθ.symm))
  have hlast : ι ≫ ((p ≫ f) ≫ t) = (s.splitting.cofan (op ⦋m⦌)).inj a ≫ (f ≫ t) :=
    (congrArg (fun z => ι ≫ z) (Category.assoc p f t)).trans
      ((Category.assoc ι p (f ≫ t)).symm.trans (congrArg (fun z => z ≫ (f ≫ t)) hι.symm))
  exact hfirst.trans (hmiddle.trans hlast)

end CommAlgCat.PolynomialSplitDegreeExtension

end
