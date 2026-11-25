/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting

/-!
# Splittings transferred through homotopy retracts

A split complex passes its generalized inverses to any homotopy retract.
For a homotopy from the identity to the retract composite the correction
has a positive sign. Transport through a homotopy equivalence uses the
negative of its composite-to-identity homotopy.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/--
Let K,L be complexes of the same arbitrary shape c in a preadditive category C, and let s be a
generalized-inverse splitting of K. Let g:L→K, f:K→L and H:1_L∼g≫f be a homotopy retract. Then
L has a splitting with component H.hom i j + g.f i ≫ s.hom i j ≫ f.f j. The homotopy
correction is positive for the stated orientation 1_L→g≫f.
-/
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

/--
Let K,L be complexes of the same arbitrary shape c in a preadditive category C, and let s be a
generalized-inverse splitting of K. Let g:L→K, f:K→L and H:1_L∼g≫f be a homotopy retract. The
transferred generalized inverse from Lᵢ to Lⱼ is exactly H.hom i j + g.f i ≫ s.hom i j ≫ f.f
j.
-/
@[simp]
theorem Splitting.ofHomotopyRetract_hom (s : Splitting K) (g : L ⟶ K) (f : K ⟶ L)
    (h : Homotopy (𝟙 L) (g ≫ f)) (i j : ι) :
    (s.ofHomotopyRetract g f h).hom i j =
      h.hom i j + g.f i ≫ s.hom i j ≫ f.f j := rfl

/--
Let K,L be complexes of the same arbitrary shape c in a preadditive category C, and let s be a
generalized-inverse splitting of K. For a homotopy equivalence e:K≃L, transport s to L using
g=e.inv, f=e.hom and the homotopy 1_L∼e.inv≫e.hom. The result is a splitting of L.
-/
def Splitting.ofHomotopyEquiv (s : Splitting K) (e : HomotopyEquiv K L) : Splitting L :=
  s.ofHomotopyRetract e.inv e.hom e.homotopyInvHomId.symm

/--
Let K,L be complexes of the same arbitrary shape c in a preadditive category C, and let s be a
generalized-inverse splitting of K. For e:K≃L, let H be its homotopy from e.inv≫e.hom to 1_L.
The transferred component is −H.hom i j + e.inv.f i ≫ s.hom i j ≫ e.hom.f j.
-/
@[simp]
theorem Splitting.ofHomotopyEquiv_hom (s : Splitting K) (e : HomotopyEquiv K L) (i j : ι) :
    (s.ofHomotopyEquiv e).hom i j =
      -e.homotopyInvHomId.hom i j + e.inv.f i ≫ s.hom i j ≫ e.hom.f j := rfl

/--
Let K,L be c-complexes in a preadditive category C. If K admits a splitting and g:L→K, f:K→L
satisfy 1_L∼g≫f, then L also admits a splitting.
-/
theorem isSplit_of_homotopyRetract (hs : IsSplit K) (g : L ⟶ K) (f : K ⟶ L)
    (h : Homotopy (𝟙 L) (g ≫ f)) : IsSplit L := by
  rcases hs with ⟨s⟩
  exact ⟨s.ofHomotopyRetract g f h⟩

/--
Let K,L be complexes of shape c in a preadditive category C. Any homotopy equivalence K≃L
gives IsSplit K↔IsSplit L, by transporting generalized-inverse splitting data in both
directions.
-/
theorem isSplit_iff_of_homotopyEquiv (e : HomotopyEquiv K L) : IsSplit K ↔ IsSplit L := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.ofHomotopyEquiv e⟩
  · rintro ⟨s⟩
    exact ⟨s.ofHomotopyEquiv e.symm⟩

/--
Let K,L be c-complexes in a preadditive category C, assume every differential of K is zero,
and let e:K≃L. Transporting the zero splitting of K gives component −e.homotopyInvHomId.hom i
j on L, with no additional transported inverse term.
-/
theorem Splitting.ofHomotopyEquiv_ofZero_hom (hK : ∀ i j, K.d i j = 0)
    (e : HomotopyEquiv K L) (i j : ι) :
    ((Splitting.ofZero hK).ofHomotopyEquiv e).hom i j =
      -e.homotopyInvHomId.hom i j := by
  simp only [ofHomotopyEquiv_hom, ofZero_hom, comp_zero, zero_comp, add_zero]

end HomologicalComplex
