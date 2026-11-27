/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialOrderedPrismShell
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitting
public import MathlibExt.AlgebraicTopology.SimplicialObject.SplittingPrismDegeneracyDescent

/-!
# Higher nondegenerate degree extension of a polynomial prism

Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, and s a compatible
polynomial splitting of P. Fix maps f,g:P→Q over A and a family of primitive prism maps on the
nondegenerate summands. Their whole-degree extensions are coproduct descents over the
epimorphisms of the simplex category.

For d∈ℕ, PreviousFaces records endpoint, exterior-face, common-middle and augmentation
identities in source degree d+1. These determine all prescribed exterior walls and corner
compatibilities in the new source degree d+2. If Q's normalized additive augmentation is a
quasi-isomorphism, polynomial shell filling produces the new nondegenerate operators
N(d+2)(P)→Q(d+3), retaining both endpoints, all exterior faces, common middles and augmentation.

The primitive family is indexed in every degree; the new degree step uses its lower-degree
restrictions. The ground-ring universe u and algebra parameter v remain independent, with
algebra diagrams and variables at the stable height max(u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialPrismNondegenerateDegreeExtension

open PolynomialOrderedPrismShell

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left)
  (p : ∀ n : ℕ, Fin (n + 1) → (s.splitting.N n ⟶ Q.left.obj (op ⦋n + 1⦌)))
  (f g : P ⟶ Q)

private theorem face_pair {C : Type*} [Category* C] (X : SimplicialObject C)
    (d j l : ℕ) (hjl : j < l) (hl : l ≤ d + 2) :
    face X (d + 1) j (by omega) ≫ face X d (l - 1) (by omega) =
      face X (d + 1) l hl ≫ face X d j (by omega) := by
  have h : (⟨j, by omega⟩ : Fin (d + 2)).castSucc < (⟨l, by omega⟩ : Fin (d + 3)) := by
    exact hjl
  have hcast : (⟨j, by omega⟩ : Fin (d + 2)).castSucc =
      (⟨j, by omega⟩ : Fin (d + 3)) := Fin.ext rfl
  have hpred : (⟨l, by omega⟩ : Fin (d + 3)).pred h.ne_zero =
      (⟨l - 1, by omega⟩ : Fin (d + 2)) := Fin.ext rfl
  have hface := (X.δ_comp_δ' (i := (⟨j, by omega⟩ : Fin (d + 2)))
    (j := (⟨l, by omega⟩ : Fin (d + 3))) h).symm
  rw [hpred, hcast] at hface
  exact hface

private theorem face_naturality (q : P ⟶ Q) (d j : ℕ) (hj : j ≤ d + 1) :
    face P.left d j hj ≫ q.left.app (op ⦋d⦌) =
      q.left.app (op ⦋d + 1⦌) ≫ face Q.left d j hj :=
  q.left.naturality (SimplexCategory.δ (⟨j, by omega⟩ : Fin (d + 2))).op

private theorem face_augmentation (d j : ℕ) (hj : j ≤ d + 1) :
    face P.left d j hj ≫ P.hom.app (op ⦋d⦌) = P.hom.app (op ⦋d + 1⦌) :=
  (P.hom.naturality (SimplexCategory.δ (⟨j, by omega⟩ : Fin (d + 2))).op).trans
    (Category.comp_id _)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. The
operator Hₙ,ᵢ:Pₙ→Qₙ₊₁ extends the nondegenerate prescription across every epimorphism-indexed
summand, for i≤n. -/
def previous (n i : ℕ) (hi : i ≤ n) :
    P.left.obj (op ⦋n⦌) ⟶ Q.left.obj (op ⦋n + 1⦌) :=
  s.splitting.prismDegree p (⟨i, Nat.lt_succ_iff.mpr hi⟩ : Fin (n + 1))

/-- Let k be a commutative ring and P an augmented simplicial k-algebra with compatible polynomial
splitting s. For each n, the map cₙ:k[Vₙ]→Pₙ is the inverse polynomial presentation of Nₙ(P)
followed by its summand inclusion. -/
def coordinate (n : ℕ) : PolynomialSource k (s.variables n) ⟶ P.left.obj (op ⦋n⦌) :=
  (s.polynomialIso n).inv ≫ s.splitting.ι n

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. For d∈ℕ,
the preceding-degree condition consists of the endpoint, early-face, late-face, common-middle
and augmentation identities for H in source degree d+1. These compare its exterior faces to the
operators in degree d. -/
structure PreviousFaces (d : ℕ) : Prop where
  /-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. In
source degree d+1, the first preceding operator satisfies H(d+1,0)≫δ₀=g(d+1). -/
  zero : previous s p (d + 1) 0 (by omega) ≫ face Q.left (d + 1) 0 (by omega) =
    g.left.app (op ⦋d + 1⦌)
  /-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. In
source degree d+1, the final preceding operator satisfies H(d+1,d+1)≫δ(d+2)=f(d+1). -/
  last : previous s p (d + 1) (d + 1) (by omega) ≫ face Q.left (d + 1) (d + 2) (by omega) =
    f.left.app (op ⦋d + 1⦌)
  /-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. For
i≤d+1 and j<i, the preceding early-face equation is H(d+1,i)≫δj=δj≫H(d,i−1), with the face on
the right belonging to P. -/
  early : ∀ (i : ℕ) (hi : i ≤ d + 1) (j : ℕ) (hj : j < i),
    previous s p (d + 1) i hi ≫ face Q.left (d + 1) j (by omega) =
      face P.left d j (by omega) ≫ previous s p d (i - 1) (by omega)
  /-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. For
i≤d+1 and i+1<j≤d+2, the preceding late-face equation is H(d+1,i)≫δj=δ(j−1)≫H(d,i), with the
face on the right belonging to P. -/
  late : ∀ (i : ℕ) (hi : i ≤ d + 1) (j : ℕ) (hj : i + 1 < j) (hj' : j ≤ d + 2),
    previous s p (d + 1) i hi ≫ face Q.left (d + 1) j hj' =
      face P.left d (j - 1) (by omega) ≫ previous s p d i (by omega)
  /-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. For
i<d+1, consecutive preceding prism maps have the common middle
H(d+1,i+1)≫δ(i+1)=H(d+1,i)≫δ(i+1). -/
  middle : ∀ (i : ℕ) (hi : i < d + 1),
    previous s p (d + 1) (i + 1) (by omega) ≫ face Q.left (d + 1) (i + 1) (by omega) =
      previous s p (d + 1) i (by omega) ≫ face Q.left (d + 1) (i + 1) (by omega)
  /-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. For
i≤d+1, H(d+1,i)≫εQ(d+2)=εP(d+1). -/
  augmentation : ∀ (i : ℕ) (hi : i ≤ d + 1),
    previous s p (d + 1) i hi ≫ Q.hom.app (op ⦋d + 2⦌) = P.hom.app (op ⦋d + 1⦌)

variable {d : ℕ}

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. For
i≤d+2 and j≤d+3, define the degree-d+2 wall Wᵢ,ⱼ:k[V(d+2)]→Q(d+2). For j<i it is
c≫δj≫H(d+1,i−1); for i+1<j it is c≫δ(j−1)≫H(d+1,i). The first endpoint is c≫g and the final
endpoint is c≫f. Other central positions use c≫g as a default. -/
def wall (i : ℕ) (hi : i ≤ d + 2) (j : ℕ) (hj : j ≤ d + 3) :
    PolynomialSource k (s.variables (d + 2)) ⟶ Q.left.obj (op ⦋d + 2⦌) :=
  if he : j < i then
    coordinate s (d + 2) ≫ face P.left (d + 1) j (by omega) ≫
      previous s p (d + 1) (i - 1) (by omega)
  else if hl : i + 1 < j then
    coordinate s (d + 2) ≫ face P.left (d + 1) (j - 1) (by omega) ≫
      previous s p (d + 1) i (by omega)
  else if hzero : i = 0 ∧ j = 0 then
    coordinate s (d + 2) ≫ g.left.app (op ⦋d + 2⦌)
  else if hlast : i = d + 2 ∧ j = d + 3 then
    coordinate s (d + 2) ≫ f.left.app (op ⦋d + 2⦌)
  else coordinate s (d + 2) ≫ g.left.app (op ⦋d + 2⦌)

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. If
j<i≤d+2, the wall is Wᵢ,ⱼ=c≫δj≫H(d+1,i−1), where c is the degree-d+2 polynomial coordinate
inclusion. -/
theorem wall_early (i : ℕ) (hi : i ≤ d + 2) (j : ℕ) (hj : j < i) :
    wall s p f g i hi j (by omega) =
      coordinate s (d + 2) ≫ face P.left (d + 1) j (by omega) ≫
        previous s p (d + 1) (i - 1) (by omega) := by
  rw [wall, dite_eq_left hj]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. If i≤d+2
and i+1<j≤d+3, the wall is Wᵢ,ⱼ=c≫δ(j−1)≫H(d+1,i). -/
theorem wall_late (i : ℕ) (hi : i ≤ d + 2) (j : ℕ) (hj : i + 1 < j) (hj' : j ≤ d + 3) :
    wall s p f g i hi j hj' =
      coordinate s (d + 2) ≫ face P.left (d + 1) (j - 1) (by omega) ≫
        previous s p (d + 1) i (by omega) := by
  rw [wall, dite_eq_right (by omega), dite_eq_left hj]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. The
first endpoint wall is W₀,₀=c≫g(d+2), on the degree-d+2 polynomial coordinates. -/
theorem wall_first : wall s p f g 0 (by omega) 0 (by omega) =
    coordinate s (d + 2) ≫ g.left.app (op ⦋d + 2⦌) := by
  rw [wall, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left ⟨rfl, rfl⟩]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. The
final endpoint wall is W(d+2,d+3)=c≫f(d+2), on the degree-d+2 polynomial coordinates. -/
theorem wall_last : wall s p f g (d + 2) (by omega) (d + 3) (by omega) =
    coordinate s (d + 2) ≫ f.left.app (op ⦋d + 2⦌) := by
  rw [wall, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left ⟨rfl, rfl⟩]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. For
j<l≤d+3, when j and l are prescribed exterior faces of prism i, their codimension-two equation
is Wᵢ,ⱼ≫δ(l−1)=Wᵢ,ₗ≫δj. -/
theorem wall_local (h : PreviousFaces s p f g d)
    (i : ℕ) (hi : i ≤ d + 2) (j l : ℕ) (hjl : j < l) (hl : l ≤ d + 3)
    (hjfix : Fixed (d + 2) i j) (hlfix : Fixed (d + 2) i l) :
    wall s p f g i hi j (by omega) ≫ face Q.left (d + 1) (l - 1) (by omega) =
      wall s p f g i hi l hl ≫ face Q.left (d + 1) j (by omega) := by
  by_cases hfirst : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := hfirst
    have hlate : 0 + 1 < l := by unfold Fixed at hlfix; omega
    rw [wall_first, wall_late s p f g 0 (by omega) l hlate hl]
    simp only [Category.assoc]
    rw [h.zero, ← face_naturality g (d + 1) (l - 1) (by omega)]
  · by_cases hlast : i = d + 2 ∧ l = d + 3
    · obtain ⟨rfl, rfl⟩ := hlast
      have hearly : j < d + 2 := by unfold Fixed at hjfix; omega
      rw [wall_early s p f g (d + 2) (by omega) j hearly, wall_last]
      have hd2 : d + 2 - 1 = d + 1 := by omega
      have hd3 : d + 3 - 1 = d + 2 := by omega
      simp only [Category.assoc, hd2, hd3]
      rw [h.last, ← face_naturality f (d + 1) j (by omega)]
    · by_cases hjearly : j < i
      · by_cases hlearly : l < i
        · rw [wall_early s p f g i hi j hjearly, wall_early s p f g i hi l hlearly]
          simp only [Category.assoc]
          rw [h.early (i - 1) (by omega) (l - 1) (by omega),
            h.early (i - 1) (by omega) j (by omega)]
          have hsub : i - 1 - 1 = i - 2 := by omega
          simp only [hsub]
          simpa only [Category.assoc] using congrArg
            (fun z => coordinate s (d + 2) ≫ z ≫ previous s p d (i - 2) (by omega))
              (face_pair P.left d j l hjl (by omega))
        · have hllate : i + 1 < l := by unfold Fixed at hlfix; omega
          rw [wall_early s p f g i hi j hjearly, wall_late s p f g i hi l hllate hl]
          simp only [Category.assoc]
          rw [h.late (i - 1) (by omega) (l - 1) (by omega) (by omega),
            h.early i (by omega) j hjearly]
          have hsub : l - 1 - 1 = l - 2 := by omega
          simp only [hsub]
          simpa only [Category.assoc, hsub] using congrArg
            (fun z => coordinate s (d + 2) ≫ z ≫ previous s p d (i - 1) (by omega))
              (face_pair P.left d j (l - 1) (by omega) (by omega))
      · have hjlate : i + 1 < j := by unfold Fixed at hjfix; omega
        have hllate : i + 1 < l := by omega
        rw [wall_late s p f g i hi j hjlate (by omega), wall_late s p f g i hi l hllate hl]
        simp only [Category.assoc]
        rw [h.late i (by omega) (l - 1) (by omega) (by omega),
          h.late i (by omega) j hjlate (by omega)]
        have hsub : l - 1 - 1 = l - 2 := by omega
        simp only [hsub]
        simpa only [Category.assoc, hsub] using congrArg
          (fun z => coordinate s (d + 2) ≫ z ≫ previous s p d i (by omega))
            (face_pair P.left d (j - 1) (l - 1) (by omega) (by omega))

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. For
i≤d+2 and j+1<i, consecutive prism walls satisfy Wᵢ,ⱼ≫δ(i−1)=W(i−1,j)≫δ(i−1). -/
theorem wall_precedingEarly (h : PreviousFaces s p f g d)
    (i : ℕ) (hi : i ≤ d + 2) (j : ℕ) (hj : j + 1 < i) :
    wall s p f g i hi j (by omega) ≫ face Q.left (d + 1) (i - 1) (by omega) =
      wall s p f g (i - 1) (by omega) j (by omega) ≫ face Q.left (d + 1) (i - 1) (by omega) := by
  rw [wall_early s p f g i hi j (by omega), wall_early s p f g (i - 1) (by omega) j (by omega)]
  have hm := h.middle (i - 2) (by omega)
  have heq : i - 2 + 1 = i - 1 := by omega
  simp only [heq] at hm
  have hsub : i - 1 - 1 = i - 2 := by omega
  simp only [hsub]
  simpa only [Category.assoc] using congrArg
    (fun z => coordinate s (d + 2) ≫ face P.left (d + 1) j (by omega) ≫ z) hm

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. For
0<i≤d+2 and i+1<j≤d+3, consecutive prism walls satisfy W(i−1,j)≫δi=Wᵢ,ⱼ≫δi. -/
theorem wall_precedingLate (h : PreviousFaces s p f g d)
    (i : ℕ) (hi : i ≤ d + 2) (hpos : 0 < i) (j : ℕ) (hj : i + 1 < j) (hj' : j ≤ d + 3) :
    wall s p f g (i - 1) (by omega) j hj' ≫ face Q.left (d + 1) i (by omega) =
      wall s p f g i hi j hj' ≫ face Q.left (d + 1) i (by omega) := by
  rw [wall_late s p f g (i - 1) (by omega) j (by omega) hj', wall_late s p f g i hi j hj hj']
  have hm := h.middle (i - 1) (by omega)
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ i)] at hm
  simpa only [Category.assoc] using congrArg
    (fun z => coordinate s (d + 2) ≫ face P.left (d + 1) (j - 1) (by omega) ≫ z) hm.symm

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. The
first corner equation is W₁,₀≫δ₀=(c≫g(d+2))≫δ₀. -/
theorem wall_firstCorner (h : PreviousFaces s p f g d) :
    wall s p f g 1 (by omega) 0 (by omega) ≫ face Q.left (d + 1) 0 (by omega) =
      (coordinate s (d + 2) ≫ g.left.app (op ⦋d + 2⦌)) ≫ face Q.left (d + 1) 0 (by omega) := by
  rw [wall_early s p f g 1 (by omega) 0 (by omega)]
  simp only [Category.assoc, Nat.sub_self]
  rw [h.zero, face_naturality g (d + 1) 0 (by omega)]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. For
2≤i≤d+2, the two-step corner equation is W(i,i−1)≫δ(i−1)=W(i−2,i)≫δ(i−1). -/
theorem wall_twoStepCorner (h : PreviousFaces s p f g d)
    (i : ℕ) (hi : i ≤ d + 2) (hpos : 2 ≤ i) :
    wall s p f g i hi (i - 1) (by omega) ≫ face Q.left (d + 1) (i - 1) (by omega) =
      wall s p f g (i - 2) (by omega) i (by omega) ≫ face Q.left (d + 1) (i - 1) (by omega) := by
  rw [wall_early s p f g i hi (i - 1) (by omega),
    wall_late s p f g (i - 2) (by omega) i (by omega) (by omega)]
  have hm := h.middle (i - 2) (by omega)
  have heq : i - 2 + 1 = i - 1 := by omega
  simp only [heq] at hm
  simpa only [Category.assoc] using congrArg
    (fun z => coordinate s (d + 2) ≫ face P.left (d + 1) (i - 1) (by omega) ≫ z) hm

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. The
last corner equation is W(d+1,d+3)≫δ(d+2)=(c≫f(d+2))≫δ(d+2). -/
theorem wall_lastCorner (h : PreviousFaces s p f g d) :
    wall s p f g (d + 1) (by omega) (d + 3) (by omega) ≫ face Q.left (d + 1) (d + 2) (by omega) =
      (coordinate s (d + 2) ≫ f.left.app (op ⦋d + 2⦌)) ≫
        face Q.left (d + 1) (d + 2) (by omega) := by
  rw [wall_late s p f g (d + 1) (by omega) (d + 3) (by omega) (by omega)]
  have hd3 : d + 3 - 1 = d + 2 := by omega
  simp only [Category.assoc, hd3]
  rw [h.last, face_naturality f (d + 1) (d + 2) (by omega)]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. Each
prescribed exterior wall satisfies Wᵢ,ⱼ≫εQ(d+2)=c≫εP(d+2), for i≤d+2 and j≤d+3. -/
theorem wall_augmentation (h : PreviousFaces s p f g d)
    (i : ℕ) (hi : i ≤ d + 2) (j : ℕ) (hj : j ≤ d + 3) (hfix : Fixed (d + 2) i j) :
    wall s p f g i hi j hj ≫ Q.hom.app (op ⦋d + 2⦌) =
      coordinate s (d + 2) ≫ P.hom.app (op ⦋d + 2⦌) := by
  rcases hfix with hearly | hlate | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [wall_early s p f g i hi j hearly]
    simp only [Category.assoc]
    rw [h.augmentation (i - 1) (by omega), face_augmentation (d + 1) j (by omega)]
  · rw [wall_late s p f g i hi j hlate hj]
    simp only [Category.assoc]
    rw [h.augmentation i (by omega), face_augmentation (d + 1) (j - 1) (by omega)]
  · rw [wall_first, Category.assoc]
    have hε : g.left.app (op ⦋d + 2⦌) ≫ Q.hom.app (op ⦋d + 2⦌) =
        P.hom.app (op ⦋d + 2⦌) := by
      simpa only [NatTrans.comp_app] using NatTrans.congr_app g.w (op ⦋d + 2⦌)
    exact congrArg (fun z => coordinate s (d + 2) ≫ z) hε
  · rw [wall_last, Category.assoc]
    have hε : f.left.app (op ⦋d + 2⦌) ≫ Q.hom.app (op ⦋d + 2⦌) =
        P.hom.app (op ⦋d + 2⦌) := by
      simpa only [NatTrans.comp_app] using NatTrans.congr_app f.w (op ⦋d + 2⦌)
    exact congrArg (fun z => coordinate s (d + 2) ≫ z) hε

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces. The
polynomial walls, endpoint maps, consecutive-wall compatibilities and corner equations define a
shell on k[V(d+2)] over A, with augmentation c≫εP(d+2). -/
def sourceShell (h : PreviousFaces s p f g d) :
    Shell k A Q (s.variables (d + 2)) (d + 1) := by
  exact {
    augmentation := coordinate s (d + 2) ≫ P.hom.app (op ⦋d + 2⦌)
    firstEndpoint := coordinate s (d + 2) ≫ g.left.app (op ⦋d + 2⦌)
    lastEndpoint := coordinate s (d + 2) ≫ f.left.app (op ⦋d + 2⦌)
    wall := wall s p f g
    first := wall_first s p f g
    last := wall_last s p f g
    compatible := wall_local s p f g h
    precedingEarly := wall_precedingEarly s p f g h
    precedingLate := wall_precedingLate s p f g h
    firstCorner := wall_firstCorner s p f g h
    twoStepCorner := wall_twoStepCorner s p f g h
    lastCorner := wall_lastCorner s p f g h
    wall_augmentation := wall_augmentation s p f g h
  }

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces.
Assume also that Q's normalized additive augmentation is a quasi-isomorphism. Filling this shell
gives maps Gᵢ:N(d+2)(P)→Q(d+3), indexed by i∈Fin(d+3), with the prescribed exterior faces,
endpoints and augmentation. -/
def generatorPrism (h : PreviousFaces s p f g d) (hQ : additiveResolutionCondition k A Q)
    (i : Fin (d + 3)) : s.splitting.N (d + 2) ⟶ Q.left.obj (op ⦋d + 3⦌) :=
  (s.polynomialIso (d + 2)).hom ≫ (sourceShell s p f g h).prism hQ i

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces.
Assume also that Q's normalized additive augmentation is a quasi-isomorphism. The first new map
satisfies G₀≫δ₀=ι(d+2)≫g(d+2), where ι is the nondegenerate summand inclusion. -/
@[reassoc]
theorem generatorPrism_first_endpoint (h : PreviousFaces s p f g d)
    (hQ : additiveResolutionCondition k A Q) :
    generatorPrism s p f g h hQ (0 : Fin (d + 3)) ≫ Q.left.δ (0 : Fin (d + 4)) =
      s.splitting.ι (d + 2) ≫ g.left.app (op ⦋d + 2⦌) := by
  rw [generatorPrism, Category.assoc, Shell.prism_first_endpoint]
  simp only [sourceShell, coordinate, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces.
Assume also that Q's normalized additive augmentation is a quasi-isomorphism. The final new map
satisfies G(d+2)≫δ(d+3)=ι(d+2)≫f(d+2). -/
@[reassoc]
theorem generatorPrism_last_endpoint (h : PreviousFaces s p f g d)
    (hQ : additiveResolutionCondition k A Q) :
    generatorPrism s p f g h hQ (Fin.last (d + 2)) ≫ Q.left.δ (Fin.last (d + 3)) =
      s.splitting.ι (d + 2) ≫ f.left.app (op ⦋d + 2⦌) := by
  rw [generatorPrism, Category.assoc, Shell.prism_last_endpoint]
  simp only [sourceShell, coordinate, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces.
Assume also that Q's normalized additive augmentation is a quasi-isomorphism. For i∈Fin(d+3),
j∈Fin(d+4) and j<i, the early-face law is Gᵢ≫δj=ι(d+2)≫δj≫H(d+1,i−1). -/
@[reassoc]
theorem generatorPrism_early_face (h : PreviousFaces s p f g d)
    (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 3)) (j : Fin (d + 4))
    (hj : j < i.castSucc) :
    generatorPrism s p f g h hQ i ≫ Q.left.δ j =
      s.splitting.ι (d + 2) ≫ face P.left (d + 1) j.val (by omega) ≫
        previous s p (d + 1) (i.val - 1) (by omega) := by
  rw [generatorPrism, Category.assoc,
    Shell.prism_fixed (sourceShell s p f g h) hQ i j (Or.inl hj)]
  change (s.polynomialIso (d + 2)).hom ≫ wall s p f g i.val (by omega) j.val (by omega) = _
  rw [wall_early s p f g i.val (by omega) j.val hj]
  simp only [coordinate, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces.
Assume also that Q's normalized additive augmentation is a quasi-isomorphism. For i∈Fin(d+3),
j∈Fin(d+4) and i+1<j, the late-face law is Gᵢ≫δj=ι(d+2)≫δ(j−1)≫H(d+1,i). -/
@[reassoc]
theorem generatorPrism_late_face (h : PreviousFaces s p f g d)
    (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 3)) (j : Fin (d + 4))
    (hj : i.val + 1 < j.val) :
    generatorPrism s p f g h hQ i ≫ Q.left.δ j =
      s.splitting.ι (d + 2) ≫ face P.left (d + 1) (j.val - 1) (by omega) ≫
        previous s p (d + 1) i.val (by
          have hiSucc : i.val + 1 < j.val := by simpa only [Fin.lt_def, Fin.val_succ] using hj
          have hjBound := j.isLt
          omega) := by
  rw [generatorPrism, Category.assoc,
    Shell.prism_fixed (sourceShell s p f g h) hQ i j (Or.inr (Or.inl hj))]
  change (s.polynomialIso (d + 2)).hom ≫ wall s p f g i.val (by omega) j.val (by omega) = _
  rw [wall_late s p f g i.val (by omega) j.val hj (by omega)]
  simp only [coordinate, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces.
Assume also that Q's normalized additive augmentation is a quasi-isomorphism. For i∈Fin(d+2),
the new maps have common middle G(i+1)≫δ(i+1)=Gᵢ≫δ(i+1). -/
@[reassoc]
theorem generatorPrism_common_middle (h : PreviousFaces s p f g d)
    (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 2)) :
    generatorPrism s p f g h hQ i.succ ≫ Q.left.δ i.castSucc.succ =
      generatorPrism s p f g h hQ i.castSucc ≫ Q.left.δ i.castSucc.succ := by
  simp only [generatorPrism, Category.assoc]
  rw [Shell.prism_common_middle]

/-- Let k be a commutative ring, P,Q augmented simplicial k-algebras over A, s a compatible
polynomial splitting of P, p a family of maps Nₙ(P)→Qₙ₊₁ indexed by i≤n, and f,g:P→Q maps over
A. Write Hₙ,ᵢ for the whole-degree operator obtained from p by the splitting coproduct. Fix d∈ℕ
and assume the preceding-degree face and augmentation equations recorded by PreviousFaces.
Assume also that Q's normalized additive augmentation is a quasi-isomorphism. Every i∈Fin(d+3)
satisfies Gᵢ≫εQ(d+3)=ι(d+2)≫εP(d+2). -/
@[reassoc]
theorem generatorPrism_augmentation (h : PreviousFaces s p f g d)
    (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 3)) :
    generatorPrism s p f g h hQ i ≫ Q.hom.app (op ⦋d + 3⦌) =
      s.splitting.ι (d + 2) ≫ P.hom.app (op ⦋d + 2⦌) := by
  rw [generatorPrism, Category.assoc, Shell.prism_augmentation]
  simp only [sourceShell, coordinate, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- For a simplicial object X in any category and natural numbers d,j with j≤d+1, this is the face
δj:X(d+1)→X(d), using the indicated natural-number bound. -/
abbrev face {C : Type*} [Category* C] (X : SimplicialObject C)
    (d j : ℕ) (hj : j ≤ d + 1) : X.obj (op ⦋d + 1⦌) ⟶ X.obj (op ⦋d⦌) :=
  X.δ ⟨j, Nat.lt_succ_iff.mpr hj⟩

end CommAlgCat.PolynomialPrismNondegenerateDegreeExtension

end
