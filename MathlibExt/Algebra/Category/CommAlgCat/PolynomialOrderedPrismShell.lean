/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialHornLift
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialBoundaryComparison

/-!
# Completion of polynomial prism shells

Fix an augmented simplicial commutative `k`-algebra `Q → const A` and a polynomial
source `k[σ]`. In positive degree `d + 1`, a prism shell specifies maps to `Q_(d+1)`
on the exterior faces, its first and last endpoints, and the codimension-two corner
and augmentation equations needed to match those faces.

For prism vertex `i`, the fixed faces are `j < i`, `i + 1 < j`, and the two endpoint
faces `(i,j) = (0,0)` and `(d + 1,d + 2)`. If the target augmentation is additively
aspherical, the shell extends to maps `H_i : k[σ] → Q_(d+2)` for `0 ≤ i ≤ d + 1`.
They have all prescribed exterior faces, common consecutive middle faces, and the
specified augmentation. A stage records a total family of maps with these laws
restricted to an initial segment; completion supplies the laws for the entire family.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat.PolynomialOrderedPrismShell

/--
The face map `d_j : X_(d+1) → X_d` for a natural index `j ≤ d + 1`, in an arbitrary
simplicial object.
-/
abbrev face {C : Type*} [Category* C] (X : SimplicialObject C)
    (d j : ℕ) (hj : j ≤ d + 1) : X.obj (op ⦋d + 1⦌) ⟶ X.obj (op ⦋d⦌) :=
  X.δ ⟨j, Nat.lt_succ_iff.mpr hj⟩

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

private theorem face_self {C : Type*} [Category* C] (X : SimplicialObject C)
    (d j : ℕ) (hj : j ≤ d + 1) :
    face X (d + 1) j (by omega) ≫ face X d j hj =
      face X (d + 1) (j + 1) (by omega) ≫ face X d j hj := by
  have hcast : (⟨j, by omega⟩ : Fin (d + 2)).castSucc =
      (⟨j, by omega⟩ : Fin (d + 3)) := Fin.ext rfl
  have hsucc : (⟨j, by omega⟩ : Fin (d + 2)).succ =
      (⟨j + 1, by omega⟩ : Fin (d + 3)) := Fin.ext rfl
  have hface := X.δ_comp_δ_self (i := (⟨j, by omega⟩ : Fin (d + 2)))
  rw [hcast, hsucc] at hface
  exact hface

/--
The condition selecting the exterior faces of prism vertex `i` in degree `n`:
`j < i ∨ i + 1 < j ∨ (i = 0 ∧ j = 0) ∨ (i = n ∧ j = n + 1)`.
-/
def Fixed (n i j : ℕ) : Prop :=
  j < i ∨ i + 1 < j ∨ (i = 0 ∧ j = 0) ∨ (i = n ∧ j = n + 1)

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)
  (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (σ : Type (max u v))

/--
The commutative `k`-algebra `k[σ]` used as the common source of the shell and prism maps.
-/
abbrev PolynomialSource := CommAlgCat.of k (MvPolynomial σ k)

/--
A shell in degree `d + 1`: a common polynomial-source augmentation, two endpoint maps,
exterior wall maps to `Q_(d+1)`, and their fixed-face, neighboring-corner, endpoint-corner,
and augmentation compatibility equations. Only fixed wall values are prescriptions.
-/
structure Shell (d : ℕ) where
  /--
  The common algebra map `k[σ] → A` for all prescribed shell walls and completed prisms.
  -/
  augmentation : PolynomialSource k σ ⟶ A
  /--
  The map `k[σ] → Q_(d+1)` prescribed as the zero face of the first completed prism.
  -/
  firstEndpoint : PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 1⦌)
  /--
  The map `k[σ] → Q_(d+1)` prescribed as the last face of the final completed prism.
  -/
  lastEndpoint : PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 1⦌)
  /--
  The wall maps `w_(i,j) : k[σ] → Q_(d+1)` for `i ≤ d + 1` and `j ≤ d + 2`.
  Their values are prescribed faces only when `Fixed (d + 1) i j` holds.
  -/
  wall : ∀ (i : ℕ), i ≤ d + 1 → ∀ (j : ℕ), j ≤ d + 2 →
    (PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 1⦌))
  /--
  The wall value `w_(0,0)` is the first endpoint map.
  -/
  first : wall 0 (by omega) 0 (by omega) = firstEndpoint
  /--
  The wall value `w_(d+1,d+2)` is the last endpoint map.
  -/
  last : wall (d + 1) (by omega) (d + 2) (by omega) = lastEndpoint
  /--
  For fixed face indices `j < l` at vertex `i`, the wall maps satisfy
  `d_(l-1) ∘ w_(i,j) = d_j ∘ w_(i,l)`.
  -/
  compatible : ∀ (i : ℕ) (hi : i ≤ d + 1) (j l : ℕ) (hjl : j < l) (hl : l ≤ d + 2),
    Fixed (d + 1) i j → Fixed (d + 1) i l →
      wall i hi j (by omega) ≫ face Q.left d (l - 1) (by omega) =
        wall i hi l hl ≫ face Q.left d j (by omega)
  /--
  For `j + 1 < i`, the walls at vertices `i` and `i - 1` have the same `(i - 1)`-st
  face: `d_(i-1) ∘ w_(i,j) = d_(i-1) ∘ w_(i-1,j)`.
  -/
  precedingEarly : ∀ (i : ℕ) (hi : i ≤ d + 1) (j : ℕ) (hj : j + 1 < i),
    wall i hi j (by omega) ≫ face Q.left d (i - 1) (by omega) =
      wall (i - 1) (by omega) j (by omega) ≫ face Q.left d (i - 1) (by omega)
  /--
  For `0 < i` and `i + 1 < j ≤ d + 2`, the walls satisfy
  `d_i ∘ w_(i-1,j) = d_i ∘ w_(i,j)`.
  -/
  precedingLate : ∀ (i : ℕ) (hi : i ≤ d + 1) (hpos : 0 < i)
    (j : ℕ) (hj : i + 1 < j) (hj' : j ≤ d + 2),
    wall (i - 1) (by omega) j hj' ≫ face Q.left d i hi =
      wall i hi j hj' ≫ face Q.left d i hi
  /--
  The zero face of `w_(1,0)` equals the zero face of the first endpoint.
  -/
  firstCorner : wall 1 (by omega) 0 (by omega) ≫ face Q.left d 0 (by omega) =
    firstEndpoint ≫ face Q.left d 0 (by omega)
  /--
  For `2 ≤ i ≤ d + 1`, the walls satisfy
  `d_(i-1) ∘ w_(i,i-1) = d_(i-1) ∘ w_(i-2,i)`.
  -/
  twoStepCorner : ∀ (i : ℕ) (hi : i ≤ d + 1) (hpos : 2 ≤ i),
    wall i hi (i - 1) (by omega) ≫ face Q.left d (i - 1) (by omega) =
      wall (i - 2) (by omega) i (by omega) ≫ face Q.left d (i - 1) (by omega)
  /--
  The `(d + 1)`-st face of `w_(d,d+2)` equals that of the last endpoint.
  -/
  lastCorner : wall d (by omega) (d + 2) (by omega) ≫ face Q.left d (d + 1) (by omega) =
    lastEndpoint ≫ face Q.left d (d + 1) (by omega)
  /--
  Every fixed wall `w_(i,j)` has the common shell augmentation to `A`.
  -/
  wall_augmentation : ∀ (i : ℕ) (hi : i ≤ d + 1) (j : ℕ) (hj : j ≤ d + 2),
    Fixed (d + 1) i j → wall i hi j hj ≫ Q.hom.app (op ⦋d + 1⦌) = augmentation

namespace Shell

variable {k A Q σ} {d : ℕ} (b : Shell k A Q σ d)

/--
A total family of maps `H_i : k[σ] → Q_(d+2)` for `i ≤ d + 1`, with fixed-wall
and augmentation equations for `i < r` and consecutive middle-face equations for
`i + 1 < r`. The laws outside this initial segment are not asserted.
-/
structure Stage (r : ℕ) where
  /--
  The family `H_i : k[σ] → Q_(d+2)` for every `i ≤ d + 1`; the stage's equations
  constrain it on the indicated initial segment.
  -/
  prism : ∀ (i : ℕ), i ≤ d + 1 → (PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 2⦌))
  /--
  For `i < r` and a fixed face `j`, the `j`-th face of `H_i` equals the prescribed
  wall `w_(i,j)`.
  -/
  wall_eq : ∀ (i : ℕ) (hi : i ≤ d + 1) (hir : i < r) (j : ℕ) (hj : j ≤ d + 2),
    Fixed (d + 1) i j →
      prism i hi ≫ face Q.left (d + 1) j hj = b.wall i hi j hj
  /--
  For `i < d + 1` and `i + 1 < r`, the completed consecutive maps have the same
  middle face: `d_(i+1) ∘ H_(i+1) = d_(i+1) ∘ H_i`.
  -/
  middle_eq : ∀ (i : ℕ) (hi : i < d + 1) (hir : i + 1 < r),
    prism (i + 1) (by omega) ≫ face Q.left (d + 1) (i + 1) (by omega) =
      prism i (by omega) ≫ face Q.left (d + 1) (i + 1) (by omega)
  /--
  For `i < r`, the prism map `H_i` has the common shell augmentation.
  -/
  augmentation_eq : ∀ (i : ℕ) (hi : i ≤ d + 1) (hir : i < r),
    prism i hi ≫ Q.hom.app (op ⦋d + 2⦌) = b.augmentation

/--
At vertex `r`, use the shell wall at each face except that, for `r > 0`, face `r`
is the `r`-th face of the preceding prism `H_(r-1)`. This supplies the shared middle
face from the preceding stage.
-/
def candidate {r : ℕ} (hr : r ≤ d + 1) (a : b.Stage r)
    (j : ℕ) (hj : j ≤ d + 2) : PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 1⦌) :=
  if h : 0 < r ∧ j = r then
    a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) r (by omega)
  else b.wall r hr j hj

private theorem candidate_fixed {r : ℕ} (hr : r ≤ d + 1) (a : b.Stage r)
    (j : ℕ) (hj : j ≤ d + 2) (hfix : Fixed (d + 1) r j) :
    b.candidate hr a j hj = b.wall r hr j hj := by
  have h : ¬ (0 < r ∧ j = r) := by unfold Fixed at hfix; omega
  simp only [candidate, dite_eq_right h]

private theorem candidate_middle {r : ℕ} (hr : r ≤ d + 1) (a : b.Stage r) (hpos : 0 < r) :
    b.candidate hr a r (by omega) =
      a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) r (by omega) := by
  unfold candidate
  rw [dite_eq_left (show 0 < r ∧ r = r from ⟨hpos, rfl⟩)]

private theorem candidate_augmentation {r : ℕ} (hr : r ≤ d + 1) (a : b.Stage r)
    (j : ℕ) (hj : j ≤ d + 2) (hvalid : j ≠ r + 1 ∨ r = d + 1) :
    b.candidate hr a j hj ≫ Q.hom.app (op ⦋d + 1⦌) = b.augmentation := by
  by_cases h : 0 < r ∧ j = r
  · rw [candidate, dite_eq_left h, Category.assoc]
    have hε : face Q.left (d + 1) r (by omega) ≫ Q.hom.app (op ⦋d + 1⦌) =
        Q.hom.app (op ⦋d + 2⦌) :=
      (Q.hom.naturality (SimplexCategory.δ (⟨r, by omega⟩ : Fin (d + 3))).op).trans
        (Category.comp_id _)
    rw [hε]
    exact a.augmentation_eq (r - 1) (by omega) (by omega)
  · rw [candidate, dite_eq_right h]
    apply b.wall_augmentation
    unfold Fixed
    omega

private theorem candidate_compatible {r : ℕ} (hr : r ≤ d + 1) (a : b.Stage r)
    (j l : ℕ) (hjl : j < l) (hl : l ≤ d + 2)
    (hjvalid : j ≠ r + 1 ∨ r = d + 1) (hlvalid : l ≠ r + 1 ∨ r = d + 1) :
    b.candidate hr a j (by omega) ≫ face Q.left d (l - 1) (by omega) =
      b.candidate hr a l hl ≫ face Q.left d j (by omega) := by
  by_cases hjcenter : 0 < r ∧ j = r
  · obtain ⟨hpos, hjcenter⟩ := hjcenter
    subst j
    rw [b.candidate_middle hr a hpos]
    have hlfix : Fixed (d + 1) r l := by unfold Fixed; omega
    rw [b.candidate_fixed hr a l hl hlfix]
    by_cases hlate : r + 1 < l
    · calc
        (a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) r (by omega)) ≫
            face Q.left d (l - 1) (by omega) =
            a.prism (r - 1) (by omega) ≫
              (face Q.left (d + 1) l hl ≫ face Q.left d r hr) := by
          rw [Category.assoc, face_pair Q.left d r l hjl hl]
        _ = b.wall (r - 1) (by omega) l hl ≫ face Q.left d r hr := by
          rw [← Category.assoc, a.wall_eq (r - 1) (by omega) (by omega) l hl (by
            unfold Fixed; omega)]
        _ = b.wall r hr l hl ≫ face Q.left d r hr := b.precedingLate r hr hpos l hlate hl
    · have hrLast : r = d + 1 := by omega
      have hlLast : l = d + 2 := by omega
      subst r
      subst l
      rw [b.last]
      calc
        (a.prism d (by omega) ≫ face Q.left (d + 1) (d + 1) (by omega)) ≫
            face Q.left d (d + 1) (by omega) =
            (a.prism d (by omega) ≫ face Q.left (d + 1) (d + 2) (by omega)) ≫
              face Q.left d (d + 1) (by omega) := by
          rw [Category.assoc, face_self Q.left d (d + 1) (by omega), ← Category.assoc]
        _ = b.wall d (by omega) (d + 2) (by omega) ≫ face Q.left d (d + 1) (by omega) := by
          rw [a.wall_eq d (by omega) (by omega) (d + 2) (by omega) (by unfold Fixed; omega)]
        _ = b.lastEndpoint ≫ face Q.left d (d + 1) (by omega) := b.lastCorner
  · by_cases hlcenter : 0 < r ∧ l = r
    · obtain ⟨hpos, hlcenter⟩ := hlcenter
      subst l
      have hjfix : Fixed (d + 1) r j := by unfold Fixed; omega
      rw [b.candidate_fixed hr a j (by omega) hjfix, b.candidate_middle hr a hpos]
      by_cases hfar : j + 1 < r
      · calc
          b.wall r hr j (by omega) ≫ face Q.left d (r - 1) (by omega) =
              b.wall (r - 1) (by omega) j (by omega) ≫ face Q.left d (r - 1) (by omega) :=
            b.precedingEarly r hr j hfar
          _ = (a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) j (by omega)) ≫
              face Q.left d (r - 1) (by omega) := by
            rw [a.wall_eq (r - 1) (by omega) (by omega) j (by omega) (by unfold Fixed; omega)]
          _ = (a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) r (by omega)) ≫
              face Q.left d j (by omega) := by
            rw [Category.assoc, face_pair Q.left d j r hjl (by omega), ← Category.assoc]
      · have hjPrev : j = r - 1 := by omega
        subst j
        by_cases hrOne : r = 1
        · subst r
          simp only [Nat.sub_self]
          calc
            b.wall 1 hr 0 (by omega) ≫ face Q.left d 0 (by omega) =
                b.firstEndpoint ≫ face Q.left d 0 (by omega) := b.firstCorner
            _ = (a.prism 0 (by omega) ≫ face Q.left (d + 1) 0 (by omega)) ≫
                face Q.left d 0 (by omega) := by
              rw [a.wall_eq 0 (by omega) (by omega) 0 (by omega) (by unfold Fixed; omega), b.first]
            _ = (a.prism 0 (by omega) ≫ face Q.left (d + 1) 1 (by omega)) ≫
                face Q.left d 0 (by omega) := by
              rw [Category.assoc, face_self Q.left d 0 (by omega), ← Category.assoc]
        · have hrTwo : 2 ≤ r := by omega
          have hpred : r - 2 + 1 = r - 1 := by omega
          have hself := face_self Q.left d (r - 1) (by omega)
          simp only [Nat.sub_add_cancel (by omega : 1 ≤ r)] at hself
          calc
            b.wall r hr (r - 1) (by omega) ≫ face Q.left d (r - 1) (by omega) =
                b.wall (r - 2) (by omega) r (by omega) ≫ face Q.left d (r - 1) (by omega) :=
              b.twoStepCorner r hr hrTwo
            _ = (a.prism (r - 2) (by omega) ≫ face Q.left (d + 1) r (by omega)) ≫
                face Q.left d (r - 1) (by omega) := by
              rw [a.wall_eq (r - 2) (by omega) (by omega) r (by omega) (by unfold Fixed; omega)]
            _ = (a.prism (r - 2) (by omega) ≫ face Q.left (d + 1) (r - 1) (by omega)) ≫
                face Q.left d (r - 1) (by omega) := by
              simpa only [Category.assoc] using
                congrArg (fun z => a.prism (r - 2) (by omega) ≫ z) hself.symm
            _ = (a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) (r - 1) (by omega)) ≫
                face Q.left d (r - 1) (by omega) := by
              have hm := a.middle_eq (r - 2) (by omega) (by omega)
              simp only [hpred] at hm
              rw [hm]
            _ = (a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) r (by omega)) ≫
                face Q.left d (r - 1) (by omega) := by
              simpa only [Category.assoc] using
                congrArg (fun z => a.prism (r - 1) (by omega) ≫ z) hself
    · have hjfix : Fixed (d + 1) r j := by unfold Fixed; omega
      have hlfix : Fixed (d + 1) r l := by unfold Fixed; omega
      rw [b.candidate_fixed hr a j (by omega) hjfix, b.candidate_fixed hr a l hl hlfix]
      exact b.compatible r hr j l hjl hl hjfix hlfix

private theorem exists_next {r : ℕ} (hr : r ≤ d + 1) (a : b.Stage r)
    (hQ : additiveResolutionCondition k A Q) :
    ∃ z : PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 2⦌),
      (∀ (j : ℕ) (hj : j ≤ d + 2), Fixed (d + 1) r j →
        z ≫ face Q.left (d + 1) j hj = b.wall r hr j hj) ∧
      (z ≫ Q.hom.app (op ⦋d + 2⦌) = b.augmentation) ∧
      (∀ hpos : 0 < r, z ≫ face Q.left (d + 1) r (by omega) =
        a.prism (r - 1) (by omega) ≫ face Q.left (d + 1) r (by omega)) := by
  let fs : Fin (d + 3) → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋d + 1⦌) :=
    fun j => (b.candidate hr a j.val (by omega)).hom
  have hz : ∃ z : PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 2⦌),
      (∀ (j : ℕ) (hj : j ≤ d + 2), j ≠ r + 1 ∨ r = d + 1 →
        z ≫ face Q.left (d + 1) j hj = b.candidate hr a j hj) ∧
      z ≫ Q.hom.app (op ⦋d + 2⦌) = b.augmentation := by
    by_cases hlast : r = d + 1
    · have hc : PolynomialBoundaryComparison.BoundaryCompatible k A Q σ (d + 1) fs := by
        intro j l hjl
        have h := congrArg CommAlgCat.Hom.hom
          (b.candidate_compatible hr a j.val l.val hjl (by omega) (Or.inr hlast) (Or.inr hlast))
        have hpred : l.pred (Fin.ne_zero_of_lt hjl) =
            (⟨l.val - 1, by omega⟩ : Fin (d + 2)) := Fin.ext rfl
        have hcast : j.castPred (Fin.ne_last_of_lt hjl) =
            (⟨j.val, by omega⟩ : Fin (d + 2)) := Fin.ext rfl
        simpa only [fs, face, CommAlgCat.hom_comp, hpred, hcast] using h
      have ha : ∀ j, (Q.hom.app (op ⦋d + 1⦌)).hom.comp (fs j) = b.augmentation.hom := by
        intro j
        exact congrArg CommAlgCat.Hom.hom
          (b.candidate_augmentation hr a j.val (by omega) (Or.inr hlast))
      let z : PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 2⦌) :=
        CommAlgCat.ofHom (PolynomialBoundaryComparison.boundaryLift k A Q σ hQ (d + 1)
          b.augmentation.hom fs hc ha)
      refine ⟨z, ?_, ?_⟩
      · intro j hj _
        apply CommAlgCat.hom_ext
        simpa only [z, fs, face, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom] using
          PolynomialBoundaryComparison.boundaryLift_faces k A Q σ hQ (d + 1)
            b.augmentation.hom fs hc ha (⟨j, by omega⟩ : Fin (d + 3))
      · apply CommAlgCat.hom_ext
        exact PolynomialBoundaryComparison.boundaryLift_augmentation k A Q σ hQ (d + 1)
          b.augmentation.hom fs hc ha
    · let hole : Fin (d + 3) := ⟨r + 1, by omega⟩
      let hs : ∀ j : Fin (d + 3), j ≠ hole →
          MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋d + 1⦌) := fun j _ => fs j
      have hc : PolynomialHornLift.Compatible k A Q σ (d + 1) hole hs := by
        intro j l hj hl hjl
        have hjv : j.val ≠ r + 1 := by
          intro h
          apply hj
          exact Fin.ext h
        have hlv : l.val ≠ r + 1 := by
          intro h
          apply hl
          exact Fin.ext h
        have h := congrArg CommAlgCat.Hom.hom
          (b.candidate_compatible hr a j.val l.val hjl (by omega) (Or.inl hjv) (Or.inl hlv))
        have hpred : l.pred (Fin.ne_zero_of_lt hjl) =
            (⟨l.val - 1, by omega⟩ : Fin (d + 2)) := Fin.ext rfl
        have hcast : j.castPred (Fin.ne_last_of_lt hjl) =
            (⟨j.val, by omega⟩ : Fin (d + 2)) := Fin.ext rfl
        simpa only [hs, fs, face, CommAlgCat.hom_comp, hpred, hcast] using h
      have ha : ∀ j hj, (Q.hom.app (op ⦋d + 1⦌)).hom.comp (hs j hj) = b.augmentation.hom := by
        intro j hj
        have hjv : j.val ≠ r + 1 := by
          intro h
          apply hj
          exact Fin.ext h
        exact congrArg CommAlgCat.Hom.hom
          (b.candidate_augmentation hr a j.val (by omega) (Or.inl hjv))
      let z : PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 2⦌) :=
        CommAlgCat.ofHom (PolynomialHornLift.lift k A Q σ (d + 1) hole b.augmentation.hom hs hc ha)
      refine ⟨z, ?_, ?_⟩
      · intro j hj hvalid
        have hjv : j ≠ r + 1 := hvalid.resolve_right hlast
        have hjhole : (⟨j, by omega⟩ : Fin (d + 3)) ≠ hole := by
          intro h
          exact hjv (congrArg Fin.val h)
        apply CommAlgCat.hom_ext
        simpa only [z, hs, fs, face, CommAlgCat.hom_comp, CommAlgCat.hom_ofHom] using
          PolynomialHornLift.lift_faces k A Q σ (d + 1) hole b.augmentation.hom hs hc ha
            (⟨j, by omega⟩ : Fin (d + 3)) hjhole
      · apply CommAlgCat.hom_ext
        exact PolynomialHornLift.lift_augmentation k A Q σ (d + 1) hole b.augmentation.hom hs hc ha
  obtain ⟨z, hfaces, haug⟩ := hz
  refine ⟨z, ?_, haug, ?_⟩
  · intro j hj hfix
    have hv : j ≠ r + 1 ∨ r = d + 1 := by unfold Fixed at hfix; omega
    rw [hfaces j hj hv, b.candidate_fixed hr a j hj hfix]
  · intro hpos
    rw [hfaces r (by omega) (Or.inl (by omega)), b.candidate_middle hr a hpos]

private def next {r : ℕ} (hr : r ≤ d + 1) (a : b.Stage r)
    (hQ : additiveResolutionCondition k A Q) : b.Stage (r + 1) := by
  let z := Classical.choose (b.exists_next hr a hQ)
  have hfaces := (Classical.choose_spec (b.exists_next hr a hQ)).1
  have haug := (Classical.choose_spec (b.exists_next hr a hQ)).2.1
  have hmiddle := (Classical.choose_spec (b.exists_next hr a hQ)).2.2
  refine {
    prism := fun i hi => if i = r then z else a.prism i hi
    wall_eq := ?_
    middle_eq := ?_
    augmentation_eq := ?_ }
  · intro i hi hir j hj hfix
    by_cases h : i = r
    · subst i
      simp only [ite_eq_left rfl]
      exact hfaces j hj hfix
    · simp only [ite_eq_right h]
      exact a.wall_eq i hi (by omega) j hj hfix
  · intro i hi hir
    have hiNe : i ≠ r := by omega
    by_cases h : i + 1 = r
    · simp only [ite_eq_left h, ite_eq_right hiNe]
      have hpos : 0 < r := by omega
      have hiEq : i = r - 1 := by omega
      subst i
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hmiddle hpos
    · simp only [ite_eq_right h, ite_eq_right hiNe]
      exact a.middle_eq i hi (by omega)
  · intro i hi hir
    by_cases h : i = r
    · subst i
      simp only [ite_eq_left rfl]
      exact haug
    · simp only [ite_eq_right h]
      exact a.augmentation_eq i hi (by omega)

private def initial : b.Stage 0 where
  prism _ _ := CommAlgCat.ofHom (MvPolynomial.aeval (fun _ => 0))
  wall_eq _ _ h := by omega
  middle_eq _ _ h := by omega
  augmentation_eq _ _ h := by omega

/--
Under additive asphericity of the target, a shell admits a stage with all required
laws through every initial segment `r ≤ d + 2`.
-/
theorem stage_exists (hQ : additiveResolutionCondition k A Q)
    (r : ℕ) (hr : r ≤ d + 2) : Nonempty (b.Stage r) := by
  revert hr
  induction r with
  | zero => intro _; exact ⟨b.initial⟩
  | succ r ih =>
    intro hr
    obtain ⟨a⟩ := ih (by omega)
    exact ⟨b.next (by omega) a hQ⟩

/--
The stage with all `d + 2` prism vertices completed, constructed under additive
asphericity of the target augmentation.
-/
def completed (hQ : additiveResolutionCondition k A Q) : b.Stage (d + 2) :=
  Classical.choice (b.stage_exists hQ (d + 2) le_rfl)

/--
The map `H_i : k[σ] → Q_(d+2)` at vertex `i : Fin (d + 2)` in the completed shell,
with its fixed-wall, middle-face, and augmentation laws.
-/
def prism (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 2)) :
    PolynomialSource k σ ⟶ Q.left.obj (op ⦋d + 2⦌) :=
  (b.completed hQ).prism i.val (Nat.lt_succ_iff.mp i.is_lt)

/--
For each fixed face index `j` of vertex `i`, the completed prism has
`d_j ∘ H_i = w_(i,j)`.
-/
@[reassoc]
theorem prism_fixed (hQ : additiveResolutionCondition k A Q)
    (i : Fin (d + 2)) (j : Fin (d + 3)) (hfix : Fixed (d + 1) i.val j.val) :
    b.prism hQ i ≫ Q.left.δ j = b.wall i.val (by omega) j.val (by omega) :=
  (b.completed hQ).wall_eq i.val (by omega) i.is_lt j.val (by omega) hfix

/--
The zero face of the first prism `H₀` equals the shell's first endpoint.
-/
@[reassoc]
theorem prism_first_endpoint (hQ : additiveResolutionCondition k A Q) :
    b.prism hQ (0 : Fin (d + 2)) ≫ Q.left.δ (0 : Fin (d + 3)) = b.firstEndpoint := by
  rw [b.prism_fixed hQ 0 0 (by unfold Fixed; simp)]
  simpa only [Fin.val_zero] using b.first

/--
The `(d + 2)`-nd face of the final prism `H_(d+1)` equals the shell's last endpoint.
-/
@[reassoc]
theorem prism_last_endpoint (hQ : additiveResolutionCondition k A Q) :
    b.prism hQ (Fin.last (d + 1)) ≫ Q.left.δ (Fin.last (d + 2)) = b.lastEndpoint := by
  rw [b.prism_fixed hQ (Fin.last (d + 1)) (Fin.last (d + 2)) (by unfold Fixed; simp)]
  simpa only [Fin.val_last] using b.last

/--
For `0 ≤ i < d + 1`, the completed prisms satisfy
`d_(i+1) ∘ H_(i+1) = d_(i+1) ∘ H_i`.
-/
@[reassoc]
theorem prism_common_middle (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 1)) :
    b.prism hQ i.succ ≫ Q.left.δ i.castSucc.succ =
      b.prism hQ i.castSucc ≫ Q.left.δ i.castSucc.succ :=
  (b.completed hQ).middle_eq i.val (by omega) (by omega)

/--
Every completed prism map `H_i` has the shell's specified augmentation `k[σ] → A`.
-/
@[reassoc]
theorem prism_augmentation (hQ : additiveResolutionCondition k A Q) (i : Fin (d + 2)) :
    b.prism hQ i ≫ Q.hom.app (op ⦋d + 2⦌) = b.augmentation :=
  (b.completed hQ).augmentation_eq i.val (by omega) i.is_lt

end Shell

end CommAlgCat.PolynomialOrderedPrismShell

end
