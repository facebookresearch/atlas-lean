/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.ColumnZeroAugmentation
public import MathlibExt.Algebra.Homology.CartanEilenberg.Comparison
public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso
public import MathlibExt.Algebra.Homology.BicomplexTotalAugmentation
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat

/-!
# The total augmentation of a Cartan–Eilenberg resolution

Let C be abelian and P a Cartan–Eilenberg resolution of a nonnegative complex L. The
term-resolution augmentations form a rowwise quasi-isomorphism from the flipped bicomplex to the
bicomplex concentrated in resolution degree zero.

Totalization gives an augmentation Tot(P.bicomplex) → L. On a summand of resolution degree zero
it is the stored term augmentation; on every positive resolution-degree summand it is zero. The
total augmentation is a quasi-isomorphism and is natural for comparisons.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

namespace CartanEilenbergResolution

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution. Its
bicomplex is indexed by resolution degree a and original degree j, with total degree a+j. The
term-resolution augmentations give a bicomplex map from P.bicomplex.flip to the bicomplex whose
original-degree-j row is concentrated on Lⱼ in resolution degree zero. -/
noncomputable def flippedAugmentation :
    P.bicomplex.flip ⟶
      HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj L := by
  unfold bicomplex
  change P.termComplex ⟶
    ((ChainComplex.single₀ C).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj L
  exact ChainComplex.ofHom
    (fun j ↦ (P.termResolution j).π)
    (fun j ↦ by
      change (P.termResolution (j + 1)).π ≫
          (ChainComplex.single₀ C).map (L.d (j + 1) j) =
        P.termComplex.d (j + 1) j ≫ (P.termResolution j).π
      rw [P.termComplex_d]
      exact (P.termDifferential_comp_π j).symm)

theorem flippedAugmentation_f (j : ℕ) :
    (flippedAugmentation P).f j = (P.termResolution j).π :=
  rfl

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution. Its
bicomplex is indexed by resolution degree a and original degree j, with total degree a+j.
Totalizing the rowwise augmentations gives a canonical chain map ε : Tot(P.bicomplex) → L, using
the total flip and concentrated-complex identifications. -/
noncomputable def totalAugmentation :
    P.bicomplex.total (ComplexShape.down ℕ) ⟶ L :=
  (P.bicomplex.totalFlipIso (ComplexShape.down ℕ)).inv ≫
    HomologicalComplex₂.totalAugmentationDownNat
      (flippedAugmentation P)

theorem flippedAugmentation_f_zero (j : ℕ) :
    ((flippedAugmentation P).f j).f 0 =
      P.termColumnZeroAugmentation.f j := by
  rw [flippedAugmentation_f, P.termColumnZeroAugmentation_f]

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution. Its
bicomplex is indexed by resolution degree a and original degree j, with total degree a+j. For j
∈ ℕ, the total summand in bidegree (0,j) maps to Lⱼ by the stored augmentation PTⱼ,₀ → Lⱼ. -/
@[reassoc]
theorem ιTotal_comp_totalAugmentation_zero (j : ℕ) :
    P.bicomplex.ιTotal (ComplexShape.down ℕ) 0 j j
        (Nat.zero_add j) ≫ P.totalAugmentation.f j =
      P.termColumnZeroAugmentation.f j := by
  unfold totalAugmentation
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_inv,
    ComplexShape.σ_down_ℕ, Nat.zero_mul, pow_zero, one_smul]
  have h :=
    HomologicalComplex₂.ιTotal_comp_totalAugmentationDownNat_zero
      (f := flippedAugmentation P) j
  have h' :
      P.bicomplex.flip.ιTotal (ComplexShape.down ℕ) j 0 j
          (Nat.add_zero j) ≫
            (HomologicalComplex₂.totalAugmentationDownNat
              (flippedAugmentation P)).f j =
        ((flippedAugmentation P).f j).f 0 ≫
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (L.X j)).hom := by
    exact h
  have hid : ((flippedAugmentation P).f j).f 0 ≫
        (HomologicalComplex.singleObjXSelf
          (ComplexShape.down ℕ) 0 (L.X j)).hom =
      ((flippedAugmentation P).f j).f 0 := by
    change ((flippedAugmentation P).f j).f 0 ≫
        𝟙 (((HomologicalComplex₂.singleMapBicomplexFunctorDownNat.obj L).X j).X 0) =
      ((flippedAugmentation P).f j).f 0
    exact Category.comp_id _
  exact h'.trans (hid.trans (flippedAugmentation_f_zero P j))

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution. Its
bicomplex is indexed by resolution degree a and original degree j, with total degree a+j. For
all a,j ∈ ℕ, the total augmentation kills the summand in bidegree (a+1,j), whose total degree is
a+1+j. -/
@[reassoc]
theorem ιTotal_comp_totalAugmentation_succ (a j : ℕ) :
    P.bicomplex.ιTotal (ComplexShape.down ℕ) (a + 1) j
        (a + 1 + j) rfl ≫
      P.totalAugmentation.f (a + 1 + j) = 0 := by
  have hzero : ((flippedAugmentation P).f j).f (a + 1) = 0 := by
    rw [flippedAugmentation_f, ProjectiveResolution.π_f_succ]
    rfl
  unfold totalAugmentation
  simp only [HomologicalComplex.comp_f]
  have h := congrArg (fun k ↦
      k ≫ (HomologicalComplex₂.totalAugmentationDownNat
        (flippedAugmentation P)).f (a + 1 + j))
    (HomologicalComplex₂.ιTotal_totalFlipIso_f_inv P.bicomplex
      (ComplexShape.down ℕ) (a + 1) j (a + 1 + j) rfl)
  have hvanish (hdeg : ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, a + 1) =
        a + 1 + j) :
      P.bicomplex.flip.ιTotal (ComplexShape.down ℕ) j (a + 1)
          (a + 1 + j) hdeg ≫
            (HomologicalComplex₂.totalAugmentationDownNat
              (flippedAugmentation P)).f (a + 1 + j) = 0 := by
    have h := HomologicalComplex₂.ιTotal_comp_totalAugmentationDownNat
      (f := flippedAugmentation P) j (a + 1) (a + 1 + j) hdeg
    simpa only [hzero, zero_comp] using h
  have hscaledFlip (hdeg : ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, a + 1) =
        a + 1 + j) :
      ((ComplexShape.σ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (a + 1) j) •
        P.bicomplex.flip.ιTotal (ComplexShape.down ℕ) j (a + 1)
          (a + 1 + j) hdeg) ≫
            (HomologicalComplex₂.totalAugmentationDownNat
              (flippedAugmentation P)).f (a + 1 + j) = 0 := by
    rw [Linear.units_smul_comp, hvanish hdeg, smul_zero]
  have hscaled (hdeg : ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, a + 1) =
        a + 1 + j) :
      ((ComplexShape.σ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (a + 1) j) •
        P.bicomplex.flip.ιTotal (ComplexShape.down ℕ) j (a + 1)
          (a + 1 + j) hdeg) ≫
            (HomologicalComplex₂.totalAugmentationDownNat
              (flippedAugmentation P)).f (a + 1 + j) =
        (0 : (P.bicomplex.X (a + 1)).X j ⟶ L.X (a + 1 + j)) :=
    hscaledFlip hdeg
  simp only [Category.assoc] at h
  exact h.trans (hscaled _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution. Its
bicomplex is indexed by resolution degree a and original degree j, with total degree a+j. For g
: L → L′, a resolution Q of L′ and a comparison F : P → Q over g, the total map satisfies ε_Q ∘
Tot(F.bicomplexHom)=g ∘ ε_P. -/
theorem Hom.totalAugmentation_naturality
    {L' : ChainComplex C ℕ}
    {Q : CartanEilenbergResolution L'}
    {g : L ⟶ L'} (F : Hom P Q g) :
    HomologicalComplex₂.total.map F.bicomplexHom
          (ComplexShape.down ℕ) ≫ Q.totalAugmentation =
      P.totalAugmentation ≫ g := by
  apply HomologicalComplex.Hom.ext
  apply funext
  intro n
  apply HomologicalComplex₂.total.hom_ext (ComplexShape.down ℕ)
  intro a j h
  cases a with
  | zero =>
      change 0 + j = n at h
      have hn : n = j := h.symm.trans (Nat.zero_add j)
      cases hn
      let j := n
      have haug :
          (F.termHom j).hom.f 0 ≫ (Q.termResolution j).π.f 0 =
            (P.termResolution j).π.f 0 ≫ g.f j := by
        simpa only [HomologicalComplex.comp_f, termResolution,
          cyclesTermBoundaryMap,
          cyclesTermBoundaryShortComplex,
          ChainComplex.single₀_map_f_zero] using
            HomologicalComplex.congr_hom (F.termHom j).augmentation 0
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      have hcalc :
          P.bicomplex.ιTotal (ComplexShape.down ℕ) 0 j j
                (Nat.zero_add j) ≫
              ((HomologicalComplex₂.total.map F.bicomplexHom
                (ComplexShape.down ℕ)).f j ≫ Q.totalAugmentation.f j) =
            P.bicomplex.ιTotal (ComplexShape.down ℕ) 0 j j
                (Nat.zero_add j) ≫
              (P.totalAugmentation.f j ≫ g.f j) := by
        calc
          P.bicomplex.ιTotal (ComplexShape.down ℕ) 0 j j
                (Nat.zero_add j) ≫
              ((HomologicalComplex₂.total.map F.bicomplexHom
                (ComplexShape.down ℕ)).f j ≫ Q.totalAugmentation.f j) =
            (F.bicomplexHom.f 0).f j ≫
              (Q.bicomplex.ιTotal (ComplexShape.down ℕ) 0 j j
                (Nat.zero_add j) ≫ Q.totalAugmentation.f j) := by
                  rw [← Category.assoc,
                    HomologicalComplex₂.ιTotal_map, Category.assoc]
          _ = P.termColumnZeroAugmentation.f j ≫ g.f j := by
                rw [Q.ιTotal_comp_totalAugmentation_zero,
                  F.bicomplexHom_f_f,
                  P.termColumnZeroAugmentation_f,
                  Q.termColumnZeroAugmentation_f]
                exact haug
          _ = P.bicomplex.ιTotal (ComplexShape.down ℕ) 0 j j
                (Nat.zero_add j) ≫
                  (P.totalAugmentation.f j ≫ g.f j) := by
                  rw [← P.ιTotal_comp_totalAugmentation_zero,
                    Category.assoc]
      exact hcalc
  | succ a =>
      change a + 1 + j = n at h
      have hn : a + 1 + j = n := h
      cases hn
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      calc
        P.bicomplex.ιTotal (ComplexShape.down ℕ) (a + 1) j
              (a + 1 + j) rfl ≫
            ((HomologicalComplex₂.total.map F.bicomplexHom
              (ComplexShape.down ℕ)).f (a + 1 + j) ≫
                Q.totalAugmentation.f (a + 1 + j)) =
          (F.bicomplexHom.f (a + 1)).f j ≫
            (Q.bicomplex.ιTotal (ComplexShape.down ℕ) (a + 1) j
              (a + 1 + j) rfl ≫
                Q.totalAugmentation.f (a + 1 + j)) := by
                  rw [← Category.assoc,
                    HomologicalComplex₂.ιTotal_map, Category.assoc]
        _ = 0 := by
              rw [Q.ιTotal_comp_totalAugmentation_succ, comp_zero]
        _ = (P.bicomplex.ιTotal (ComplexShape.down ℕ) (a + 1) j
              (a + 1 + j) rfl ≫
                P.totalAugmentation.f (a + 1 + j)) ≫
                  g.f (a + 1 + j) := by
              rw [P.ιTotal_comp_totalAugmentation_succ, zero_comp]
        _ = P.bicomplex.ιTotal (ComplexShape.down ℕ) (a + 1) j
              (a + 1 + j) rfl ≫
                (P.totalAugmentation.f (a + 1 + j) ≫
                  g.f (a + 1 + j)) :=
              Category.assoc _ _ _

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution. Its
bicomplex is indexed by resolution degree a and original degree j, with total degree a+j. The
canonical augmentation Tot(P.bicomplex) → L induces an isomorphism on every nonnegative homology
object, hence is a quasi-isomorphism. -/
theorem totalAugmentation_quasiIso : QuasiIso P.totalAugmentation := by
  have hrow : ∀ j : ℕ, QuasiIso ((flippedAugmentation P).f j) := by
    intro j
    rw [flippedAugmentation_f]
    exact (P.termResolution j).quasiIso
  let _ : QuasiIso
      (HomologicalComplex₂.total.map (flippedAugmentation P)
        (ComplexShape.down ℕ)) :=
    HomologicalComplex₂.quasiIso_totalMap_of_objwise_firstQuadrant
      (flippedAugmentation P) hrow
  unfold totalAugmentation HomologicalComplex₂.totalAugmentationDownNat
  infer_instance

end CartanEilenbergResolution

end HomologicalComplex

end
