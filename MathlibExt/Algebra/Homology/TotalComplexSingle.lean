/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive
public import MathlibExt.Algebra.Homology.TotalComplexSingleDownNat
public import MathlibExt.Algebra.Homology.TotalComplexSingleRowUpNat
public import MathlibExt.Algebra.Homology.TotalComplexUpNat

/-!
# Totals of componentwise single complexes

Let C be preadditive with a zero object and finite coproducts. Placing each term of a
nonnegative chain or cochain complex L in inner degree zero gives a bicomplex whose diagonal
direct-sum total is naturally isomorphic to L. The comparison sends the summand in bidegree
(n,0) to L_n through its single-complex identification, and all other summands are zero.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- Let C be preadditive with a zero object. The functor singleMapBicomplexFunctorUpNat sends a
nonnegative cochain complex L to the bicomplex B with outer degree-p row the cochain complex
concentrated on L_p in inner degree zero. Its maps and outer differentials are obtained from
those of L. -/
noncomputable abbrev singleMapBicomplexFunctorUpNat :
    CochainComplex C ℕ ⥤
      HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (HomologicalComplex.single C (ComplexShape.up ℕ) 0).mapHomologicalComplex
    (ComplexShape.up ℕ)

/-- Let C be preadditive with a zero object. The functor singleMapBicomplexFunctorDownNat sends a
nonnegative chain complex L to the bicomplex B with outer degree-p row the chain complex
concentrated on L_p in inner degree zero. Its maps and outer differentials come from L. -/
noncomputable abbrev singleMapBicomplexFunctorDownNat :
    ChainComplex C ℕ ⥤
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (ChainComplex.single₀ C).mapHomologicalComplex (ComplexShape.down ℕ)

/-- Let C be preadditive with a zero object and finite coproducts. For a nonnegative cochain complex
L, the total complex of its componentwise degree-zero bicomplex B is canonically isomorphic to
L. In degree n the forward map identifies B_{n,0} with L_n and the inverse includes that
summand. -/
noncomputable def singleMapTotalIsoUpNat (L : CochainComplex C ℕ) :
    HomologicalComplex₂.total
      (((HomologicalComplex.single C (ComplexShape.up ℕ) 0).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L :
          HomologicalComplex₂ C (ComplexShape.up ℕ)
            (ComplexShape.up ℕ)) (ComplexShape.up ℕ) ≅ L := by
  let B : HomologicalComplex₂ C (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) :=
    ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj L
  let homComponent : ∀ (n j a : ℕ) (_ : j + a = n),
      ((B.X j).X a ⟶ L.X n) := fun n j a h ↦ by
    if ha : a = 0 then
      subst a
      subst n
      exact (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℕ) 0 (L.X j)).hom
    else
      exact 0
  let homX : ∀ n : ℕ, (B.total (ComplexShape.up ℕ)).X n ⟶
      L.X n := fun n ↦ B.totalDesc
        (fun j a h ↦ homComponent n j a h)
  let invX : ∀ n : ℕ, L.X n ⟶
      (B.total (ComplexShape.up ℕ)).X n := fun n ↦
    (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℕ) 0 (L.X n)).inv ≫
      B.ιTotal (ComplexShape.up ℕ) n 0 n rfl
  let e : ∀ n : ℕ, (B.total (ComplexShape.up ℕ)).X n ≅
      L.X n := fun n ↦
    { hom := homX n
      inv := invX n
      hom_inv_id := by
        apply HomologicalComplex₂.total.hom_ext
        intro j a h
        cases a with
        | zero =>
            have hj : j = n := h
            subst j
            have hh : h = rfl := Subsingleton.elim _ _
            cases hh
            dsimp only [homX, invX]
            rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
            dsimp only [homComponent]
            rw [dite_eq_left rfl]
            simp only [Iso.hom_inv_id_assoc, Category.comp_id]
        | succ a =>
            exact (HomologicalComplex.isZero_single_obj_X
              (ComplexShape.up ℕ) 0 (L.X j) (a + 1)
                (Nat.succ_ne_zero a)).eq_of_src _ _
      inv_hom_id := by
        dsimp only [homX, invX]
        rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
        dsimp only [homComponent]
        exact (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℕ) 0 (L.X n)).inv_hom_id }
  exact HomologicalComplex.Hom.isoOfComponents e (fun n n' hnn' ↦ by
    apply HomologicalComplex₂.total.hom_ext
    intro j a h
    cases a with
    | zero =>
        have hj : j = n := h
        subst j
        dsimp only [e, homX]
        rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
        change (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 (L.X n)).hom ≫ L.d n n' = _
        conv_rhs => rw [← Category.assoc]
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
          HomologicalComplex₂.ι_D₁,
          HomologicalComplex₂.ι_D₂,
          Preadditive.add_comp]
        rw [B.d₂_eq (ComplexShape.up ℕ) n (i₂ := 0) (i₂' := 1)
          (by simp) n'
          (by simpa using hnn')]
        have hd : (B.X n).d 0 1 = 0 := by
          apply HomologicalComplex.single_obj_d
        rw [hd, zero_comp, smul_zero, zero_comp, add_zero]
        rw [B.d₁_eq (ComplexShape.up ℕ) hnn' 0 n'
          rfl]
        have heps : ComplexShape.ε₁ (ComplexShape.up ℕ)
            (ComplexShape.up ℕ) (ComplexShape.up ℕ) (n, 0) = 1 := rfl
        rw [heps, one_smul, Category.assoc,
          HomologicalComplex₂.ι_totalDesc]
        change (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 (L.X n)).hom ≫ L.d n n' =
          (B.d n n').f 0 ≫
            homComponent n' n' 0 rfl
        dsimp only [homComponent]
        rw [dite_eq_left rfl]
        change (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 (L.X n)).hom ≫ L.d n n' =
          ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).map (L.d n n')).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℕ) 0 (L.X n')).hom
        rw [HomologicalComplex.single_map_f_self]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    | succ a =>
        exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℕ) 0 (L.X j) (a + 1)
            (Nat.succ_ne_zero a)).eq_of_src _ _)

/-- Let C be preadditive with a zero object and finite coproducts. Let L be a nonnegative cochain
complex, B its componentwise degree-zero bicomplex and e : Tot(B) ≅ L the canonical comparison.
For j ∈ ℕ, one has ι_{j,0} ≫ e.hom_j = id_{L_j}. -/
@[reassoc]
theorem ιTotal_comp_singleMapTotalIsoUpNat_hom
    (L : CochainComplex C ℕ) (j : ℕ) :
    HomologicalComplex₂.ιTotal
        (((HomologicalComplex.single C (ComplexShape.up ℕ) 0).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj L :
            HomologicalComplex₂ C (ComplexShape.up ℕ)
              (ComplexShape.up ℕ))
        (ComplexShape.up ℕ) j 0 j (Nat.add_zero j) ≫
      (singleMapTotalIsoUpNat L).hom.f j = 𝟙 (L.X j) := by
  unfold singleMapTotalIsoUpNat
  dsimp only [HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

/-- Let C be preadditive with a zero object and finite coproducts. Let L be a nonnegative cochain
complex, B its componentwise degree-zero bicomplex and e : Tot(B) ≅ L. For j ∈ ℕ, ι_{j,0} ≫
e.hom_j is the canonical identification from the degree-zero term of the single complex on L_j
to L_j. -/
@[reassoc]
theorem ιTotal_comp_singleMapTotalIsoUpNat_hom_single
    (L : CochainComplex C ℕ) (j : ℕ) :
    HomologicalComplex₂.ιTotal
        (singleMapBicomplexFunctorUpNat.obj L)
        (ComplexShape.up ℕ) j 0 j (Nat.add_zero j) ≫
      (singleMapTotalIsoUpNat L).hom.f j =
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.up ℕ) 0 (L.X j)).hom := by
  unfold singleMapTotalIsoUpNat
  dsimp only [HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

/-- Let C be preadditive with a zero object and finite coproducts. Let L be a nonnegative chain
complex, B its componentwise degree-zero bicomplex and e : Tot(B) ≅ L. For j ∈ ℕ, ι_{j,0} ≫
e.hom_j is the canonical identification from the degree-zero term of the single complex on L_j
to L_j. -/
@[reassoc]
theorem ιTotal_comp_singleMapTotalIsoDownNat_hom_single
    (L : ChainComplex C ℕ) (j : ℕ) :
    HomologicalComplex₂.ιTotal
        (singleMapBicomplexFunctorDownNat.obj L)
        (ComplexShape.down ℕ) j 0 j (Nat.add_zero j) ≫
      (single₀MapTotalIso L).hom.f j =
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) 0 (L.X j)).hom := by
  unfold single₀MapTotalIso
  dsimp only [HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [HomologicalComplex₂.ι_totalDesc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let C be preadditive with a zero object and finite coproducts. For a map f : L → L′ of
nonnegative cochain complexes, let B(f) be its componentwise degree-zero bicomplex map and
e_L,e_L′ the total comparisons. Then Tot(B(f)) ≫ e_L′.hom = e_L.hom ≫ f. -/
theorem singleMapTotalIsoUpNat_hom_naturality
    {L L' : CochainComplex C ℕ} (f : L ⟶ L') :
    HomologicalComplex₂.total.map
          (singleMapBicomplexFunctorUpNat.map f) (ComplexShape.up ℕ) ≫
        (singleMapTotalIsoUpNat L').hom =
      (singleMapTotalIsoUpNat L).hom ≫ f := by
  dsimp only [singleMapBicomplexFunctorUpNat]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro j a h
  cases a with
  | zero =>
      have hj : j = n := h
      subst j
      simp only [HomologicalComplex.comp_f,
        HomologicalComplex₂.ιTotal_map_assoc,
        ιTotal_comp_singleMapTotalIsoUpNat_hom_assoc,
        ιTotal_comp_singleMapTotalIsoUpNat_hom]
      rw [Functor.mapHomologicalComplex_map_f]
      change ((HomologicalComplex.single C (ComplexShape.up ℕ) 0).map
          (f.f n)).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.up ℕ) 0 (L'.X n)).hom =
        (HomologicalComplex.singleObjXSelf
            (ComplexShape.up ℕ) 0 (L.X n)).hom ≫ f.f n
      rw [HomologicalComplex.single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
  | succ a =>
      exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℕ) 0 (L.X j) (a + 1)
          (Nat.succ_ne_zero a)).eq_of_src _ _

/-- Let C be preadditive with a zero object and finite coproducts. The composite functor sending a
nonnegative cochain complex to its componentwise degree-zero bicomplex and then taking the total
is naturally isomorphic to the identity functor. Its component at L is singleMapTotalIsoUpNat L. -/
noncomputable def singleMapTotalNatIsoUpNat :
    singleMapBicomplexFunctorUpNat (C := C) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.up ℕ)
          (ComplexShape.up ℕ) (ComplexShape.up ℕ) ≅
      𝟭 (CochainComplex C ℕ) :=
  NatIso.ofComponents singleMapTotalIsoUpNat
    singleMapTotalIsoUpNat_hom_naturality

set_option backward.isDefEq.respectTransparency false in
/-- Let C be preadditive with a zero object and finite coproducts. For a map f : L → L′ of
nonnegative chain complexes, let B(f) be the induced componentwise degree-zero bicomplex map and
e_L,e_L′ the total comparisons. Then Tot(B(f)) ≫ e_L′.hom = e_L.hom ≫ f. -/
theorem singleMapTotalIsoDownNat_hom_naturality
    {L L' : ChainComplex C ℕ} (f : L ⟶ L') :
    HomologicalComplex₂.total.map
          (singleMapBicomplexFunctorDownNat.map f)
          (ComplexShape.down ℕ) ≫
        (single₀MapTotalIso L').hom =
      (single₀MapTotalIso L).hom ≫ f := by
  dsimp only [singleMapBicomplexFunctorDownNat]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro j a h
  cases a with
  | zero =>
      have hj : j = n := h
      subst j
      simp only [HomologicalComplex.comp_f,
        HomologicalComplex₂.ιTotal_map_assoc,
        ιTotal_comp_single₀MapTotalIso_hom_assoc,
        ιTotal_comp_single₀MapTotalIso_hom]
      rw [Functor.mapHomologicalComplex_map_f]
      change ((HomologicalComplex.single C (ComplexShape.down ℕ) 0).map
          (f.f n)).f 0 ≫
            (HomologicalComplex.singleObjXSelf
              (ComplexShape.down ℕ) 0 (L'.X n)).hom =
        (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (L.X n)).hom ≫ f.f n
      rw [HomologicalComplex.single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
  | succ a =>
      exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 (L.X j) (a + 1)
          (Nat.succ_ne_zero a)).eq_of_src _ _

/-- Let C be preadditive with a zero object and finite coproducts. The composite functor taking a
nonnegative chain complex to its componentwise degree-zero bicomplex and then totalizing is
naturally isomorphic to the identity. Its component at L is the canonical isomorphism
single₀MapTotalIso L. -/
noncomputable def singleMapTotalNatIsoDownNat :
    singleMapBicomplexFunctorDownNat (C := C) ⋙
        HomologicalComplex₂.totalFunctor C (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (ComplexShape.down ℕ) ≅
      𝟭 (ChainComplex C ℕ) :=
  NatIso.ofComponents single₀MapTotalIso
    singleMapTotalIsoDownNat_hom_naturality

end HomologicalComplex₂

end
