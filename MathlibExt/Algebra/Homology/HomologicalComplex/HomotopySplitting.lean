/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting

/-!
# Splitting transport along homotopy retracts

A one-sided homotopy retract of a split complex is split. The transported
inverse family includes the actual homotopy correction; no homology data,
abelian-category structure, zero object or second retract homotopy is needed.
The native homotopy convention fixes the sign of this correction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- A one-sided homotopy retract inherits actual generalized inverse data.
The correction is positive for a homotopy from identity to the retract map. -/
def Splitting.ofHomotopyRetract (s : Splitting K) (g : L ⟶ K) (f : K ⟶ L)
    (h : Homotopy (𝟙 L) (g ≫ f)) : Splitting L where
  hom i j := h.hom i j + g.f i ≫ s.hom i j ≫ f.f j
  zero i j hij := by
    simp only [h.zero i j hij, s.zero i j hij, comp_zero, zero_comp, add_zero]
  d_h_d i j := by
    by_cases hij : c.Rel i j
    · have hd : L.d i j ≫ dNext j h.hom = 0 := by
        change L.d i j ≫ (L.d j (c.next j) ≫ h.hom (c.next j) j) = 0
        rw [← Category.assoc, L.d_comp_d, zero_comp]
      have hp : prevD j h.hom = h.hom j i ≫ L.d i j := prevD_eq h.hom hij
      have he := congrArg (fun a : L.X j ⟶ L.X j => L.d i j ≫ a) (h.comm j)
      simp only [HomologicalComplex.id_f, Category.comp_id,
        Preadditive.comp_add] at he
      rw [hd, zero_add, hp] at he
      have ht : L.d i j ≫ (g.f j ≫ s.hom j i ≫ f.f i) ≫ L.d i j =
          L.d i j ≫ (g ≫ f).f j := by
        calc
          _ = (L.d i j ≫ g.f j) ≫ s.hom j i ≫ (f.f i ≫ L.d i j) := by
            simp only [Category.assoc]
          _ = (g.f i ≫ K.d i j) ≫ s.hom j i ≫ (K.d i j ≫ f.f j) := by
            rw [← g.comm i j, f.comm i j]
          _ = g.f i ≫ (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ f.f j := by
            simp only [Category.assoc]
          _ = g.f i ≫ K.d i j ≫ f.f j := by rw [s.d_h_d i j]
          _ = L.d i j ≫ g.f j ≫ f.f j := by
            simpa only [Category.assoc] using
              congrArg (fun a : L.X i ⟶ K.X j => a ≫ f.f j) (g.comm i j)
          _ = L.d i j ≫ (g ≫ f).f j := rfl
      calc
        _ = (L.d i j ≫ h.hom j i ≫ L.d i j) +
            (L.d i j ≫ (g.f j ≫ s.hom j i ≫ f.f i) ≫ L.d i j) := by
          simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
        _ = (L.d i j ≫ h.hom j i ≫ L.d i j) + L.d i j ≫ (g ≫ f).f j := by
          rw [ht]
        _ = L.d i j := by simpa only [Category.assoc] using he.symm
    · simp only [L.shape i j hij, comp_zero]

/-- The inherited family uses exactly the supplied homotopy and transported inverse. -/
@[simp]
theorem Splitting.ofHomotopyRetract_hom (s : Splitting K) (g : L ⟶ K) (f : K ⟶ L)
    (h : Homotopy (𝟙 L) (g ≫ f)) (i j : ι) :
    (s.ofHomotopyRetract g f h).hom i j =
      h.hom i j + g.f i ≫ s.hom i j ≫ f.f j := rfl

/-- Splitting transport along a native homotopy equivalence uses its target-side homotopy. -/
def Splitting.ofHomotopyEquiv (s : Splitting K) (e : HomotopyEquiv K L) : Splitting L :=
  s.ofHomotopyRetract e.inv e.hom e.homotopyInvHomId.symm

/-- The native composition-to-identity homotopy contributes its negative components. -/
@[simp]
theorem Splitting.ofHomotopyEquiv_hom (s : Splitting K) (e : HomotopyEquiv K L) (i j : ι) :
    (s.ofHomotopyEquiv e).hom i j =
      -e.homotopyInvHomId.hom i j + e.inv.f i ≫ s.hom i j ≫ e.hom.f j := rfl

/-- Literal splitting descends along a one-sided homotopy retract. -/
theorem isSplit_of_homotopyRetract (hs : IsSplit K) (g : L ⟶ K) (f : K ⟶ L)
    (h : Homotopy (𝟙 L) (g ≫ f)) : IsSplit L := by
  rcases hs with ⟨s⟩
  exact ⟨s.ofHomotopyRetract g f h⟩

/-- Literal splitting is invariant under any native homotopy equivalence. -/
theorem isSplit_iff_of_homotopyEquiv (e : HomotopyEquiv K L) : IsSplit K ↔ IsSplit L := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.ofHomotopyEquiv e⟩
  · rintro ⟨s⟩
    exact ⟨s.ofHomotopyEquiv e.symm⟩

/-- A zero-differential source leaves precisely the native target homotopy correction. -/
theorem Splitting.ofHomotopyEquiv_ofZero_hom (hK : ∀ i j, K.d i j = 0)
    (e : HomotopyEquiv K L) (i j : ι) :
    ((Splitting.ofZero hK).ofHomotopyEquiv e).hom i j =
      -e.homotopyInvHomId.hom i j := by
  simp only [ofHomotopyEquiv_hom, ofZero_hom, comp_zero, zero_comp, add_zero]

end HomologicalComplex
