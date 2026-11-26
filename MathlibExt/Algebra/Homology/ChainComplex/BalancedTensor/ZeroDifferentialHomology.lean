/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/
module

public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor
public import MathlibExt.Algebra.Homology.ChainComplex.NativeShift
public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesComplex
public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Balanced tensor homology with a zero-differential factor

Let R be an arbitrary ring, A a graded right-module family and Q an
integer-indexed left-module chain complex. Put the zero differential on A.
The balanced tensor total is the coproduct of columns with terms
A_p⊗_R Q_{n−p} in total degree n and differential
(−1)^p·(1⊗d_Q), using the integer sign also for negative p.

If each coefficient tensor functor A_p⊗_R− preserves homology, the
canonical comparison is
⊕_{p+q=n} A_p⊗_R H_q(Q) ≅ H_n(Tot(A_0,Q)).
It sends a coefficient tensored with a cycle class to the class of
the same tensor in the total complex. The antidiagonal is the full
integer antidiagonal.

For independent carrier universes, the comparison uses coefficient lifts
to T=max(u,v,w,t), assuming homology preservation by the lifted
coefficient functors at that height.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace ChainComplex.BalancedTensor

universe u v w t

variable (R : Type u) [Ring R]

local notation "c" => ComplexShape.down ℤ

private noncomputable instance hasMapBifunctor
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (ModuleCat.BalancedTensor.groupBifunctor R) c := by
  intro n
  infer_instance

/-- For an arbitrary ring R and an integer-graded family A of right
R-modules, the integer chain complex A_0 with term A_p in degree p
and all differentials zero. -/
abbrev zeroDifferentialComplex (A : ℤ → ModuleCat.{v} Rᵐᵒᵖ) :
    ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ :=
  (HomologicalComplex.zeroDifferentialFunctor c).obj A

variable (A : ℤ → ModuleCat.{v} Rᵐᵒᵖ)
  (Q : ChainComplex (ModuleCat.{v} R) ℤ)

private abbrev coefficientComplex (p : ℤ) : ChainComplex AddCommGrpCat.{v} ℤ :=
  (((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).mapHomologicalComplex c).obj Q

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential.

The signed p-th column has term A_p⊗_R Q_{n−p} in degree n and differential (−1)^p·(1⊗d_Q). It is the coefficient complex shifted by p. -/
def zeroDifferentialTensorColumn (p : ℤ) : ChainComplex AddCommGrpCat.{v} ℤ :=
  (ChainComplex.nativeShift AddCommGrpCat.{v} p).obj
    ((((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).mapHomologicalComplex c).obj Q)

private abbrev columnXIso (p n q : ℤ) (h : n - p = q) :
    (zeroDifferentialTensorColumn R A Q p).X n ≅
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).obj (Q.X q) :=
  ChainComplex.nativeShiftObjXIso' (coefficientComplex R A Q p) p n q h

private abbrev tensorι (p q n : ℤ) (h : p + q = n) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).obj (Q.X q) ⟶
      (complex R (zeroDifferentialComplex R A) Q).X n :=
  HomologicalComplex.ιMapBifunctor (zeroDifferentialComplex R A) Q
    (ModuleCat.BalancedTensor.groupBifunctor R) c p q n h

private lemma tensorι_d (p q n : ℤ) (h : p + q = n) :
    tensorι R A Q p q n h ≫
        (complex R (zeroDifferentialComplex R A) Q).d n (n - 1) =
      p.negOnePow •
        (((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map
          (Q.d q (q - 1)) ≫ tensorι R A Q p (q - 1) (n - 1) (by omega)) := by
  change HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ ≫
      (HomologicalComplex.mapBifunctor _ _ _ _).d _ _ = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq
      (by change (p - 1) + 1 = p; omega) q (n - 1) (by change (p - 1) + q = n - 1; omega),
    HomologicalComplex.mapBifunctor.d₂_eq p
      (by change (q - 1) + 1 = q; omega) (n - 1) (by change p + (q - 1) = n - 1; omega)]
  change _ •
      (((ModuleCat.BalancedTensor.groupBifunctor R).map
        (0 : A p ⟶ A (p - 1))).app (Q.X q) ≫ _) + _ = _
  simp only [Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero, zero_add]
  rfl

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential.

The canonical chain map from the p-th signed column to T(A,Q), given in degree n by the (p,n−p) tensor-summand inclusion. -/
def zeroDifferentialTensorColumnι (p : ℤ) :
    zeroDifferentialTensorColumn R A Q p ⟶ complex R (zeroDifferentialComplex R A) Q :=
  ChainComplex.ofHom
    (fun n =>
      (ChainComplex.nativeShiftObjXIso'
        ((((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).mapHomologicalComplex c).obj Q)
        p n (n - p) rfl).hom ≫
      HomologicalComplex.ιMapBifunctor (zeroDifferentialComplex R A) Q
        (ModuleCat.BalancedTensor.groupBifunctor R) c p (n - p) n (by omega)) (by
    intro n
    apply (cancel_epi (columnXIso R A Q p (n + 1) (n + 1 - p) rfl).inv).1
    have hs := congrArg
      (fun f => f ≫ tensorι R A Q p (n - p) n (by omega))
      (ChainComplex.nativeShiftObjXIso'_inv_d_hom (coefficientComplex R A Q p)
        p (n + 1) n (n + 1 - p) (n - p) rfl rfl)
    calc
      _ = tensorι R A Q p (n + 1 - p) (n + 1) (by omega) ≫
          (complex R (zeroDifferentialComplex R A) Q).d (n + 1) n := by
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = (p.negOnePow •
          ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map
            (Q.d (n + 1 - p) (n - p))) ≫
          tensorι R A Q p (n - p) n (by omega) := by
            have hq : n + 1 - p - 1 = n - p := by omega
            have hn : n + 1 - 1 = n := by omega
            simpa only [hq, hn, Linear.units_smul_comp] using
              tensorι_d R A Q p (n + 1 - p) (n + 1) (by omega)
      _ = _ := by simpa only [Category.assoc] using hs.symm)

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential.

The diagram of signed columns indexed by Discrete(ℤ), containing every column p. -/
def zeroDifferentialTensorColumns : Discrete ℤ ⥤ ChainComplex AddCommGrpCat.{v} ℤ :=
  Discrete.functor (zeroDifferentialTensorColumn R A Q)

private def columnsCocone : Cocone (zeroDifferentialTensorColumns R A Q) :=
  ⟨complex R (zeroDifferentialComplex R A) Q,
    Discrete.natTrans (fun p => zeroDifferentialTensorColumnι R A Q p.as)⟩

private def columnsCoconeIsColimit : IsColimit (columnsCocone R A Q) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  refine
    { desc := fun s => HomologicalComplex.mapBifunctorDesc
        (K₁ := zeroDifferentialComplex R A) (K₂ := Q)
        (F := ModuleCat.BalancedTensor.groupBifunctor R) (c := c) (j := n)
        (fun p q h => (columnXIso R A Q p n q (by change p + q = n at h; omega)).inv ≫
          s.ι.app ⟨p⟩)
      fac := ?_
      uniq := ?_ }
  · intro s ⟨p⟩
    change ((columnXIso R A Q p n (n - p) rfl).hom ≫
      tensorι R A Q p (n - p) n (by omega)) ≫ _ = _
    rw [Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    simp only [Iso.hom_inv_id_assoc]
  · intro s m hm
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := zeroDifferentialComplex R A) (K₂ := Q)
      (F := ModuleCat.BalancedTensor.groupBifunctor R) (c := c)
    intro p q h
    have hq : q = n - p := by change p + q = n at h; omega
    subst q
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    have hp := congrArg
      (fun f => (columnXIso R A Q p n (n - p) rfl).inv ≫ f) (hm ⟨p⟩)
    change _ = (columnXIso R A Q p n (n - p) rfl).inv ≫ s.ι.app ⟨p⟩
    simpa only [columnsCocone, zeroDifferentialTensorColumnι,
      Functor.mapCocone_ι_app, HomologicalComplex.eval_map, Discrete.natTrans_app,
      Category.assoc, Iso.inv_hom_id_assoc] using hp

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential.

The canonical isomorphism from the coproduct of all signed columns to the full balanced tensor total T(A,Q). -/
@[no_expose]
def zeroDifferentialTensorColumnsIso :
    colimit (zeroDifferentialTensorColumns R A Q) ≅
      complex R (zeroDifferentialComplex R A) Q :=
  colimit.isoColimitCocone ⟨columnsCocone R A Q, columnsCoconeIsColimit R A Q⟩

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential.

The coproduct injection of column p followed by the column-total isomorphism equals its canonical inclusion into T(A,Q). -/
@[reassoc]
theorem ι_zeroDifferentialTensorColumnsIso_hom (p : ℤ) :
    colimit.ι (zeroDifferentialTensorColumns R A Q) ⟨p⟩ ≫
        (zeroDifferentialTensorColumnsIso R A Q).hom =
      zeroDifferentialTensorColumnι R A Q p := by
  exact colimit.isoColimitCocone_ι_hom _ ⟨p⟩

private lemma down_prev (n : ℤ) : (ComplexShape.down ℤ).prev n = n + 1 :=
  (ComplexShape.down ℤ).prev_eq' (by change n + 1 = n + 1; rfl)

private lemma down_next (n : ℤ) : (ComplexShape.down ℤ).next n = n - 1 :=
  (ComplexShape.down ℤ).next_eq' (by change n - 1 + 1 = n; omega)

private def columnScIso (p n q : ℤ) (h : n - p = q) :
    (zeroDifferentialTensorColumn R A Q p).sc n ≅
      (coefficientComplex R A Q p).sc q :=
  (zeroDifferentialTensorColumn R A Q p).isoSc' (n + 1) n (n - 1)
      (down_prev n) (down_next n) ≪≫
    ShortComplex.isoMk
      (p.negOnePow • columnXIso R A Q p (n + 1) (q + 1) (by omega))
      (columnXIso R A Q p n q h)
      (p.negOnePow⁻¹ • columnXIso R A Q p (n - 1) (q - 1) (by omega))
      (by
        change (p.negOnePow • (columnXIso R A Q p (n + 1) (q + 1) _).hom) ≫
            (coefficientComplex R A Q p).d (q + 1) q =
          (zeroDifferentialTensorColumn R A Q p).d (n + 1) n ≫
            (columnXIso R A Q p n q h).hom
        rw [ChainComplex.nativeShiftObjXIso'_d (coefficientComplex R A Q p)
          p (n + 1) n (q + 1) q (by omega) h]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Linear.units_smul_comp, Linear.comp_units_smul])
      (by
        change (columnXIso R A Q p n q h).hom ≫
            (coefficientComplex R A Q p).d q (q - 1) =
          (zeroDifferentialTensorColumn R A Q p).d n (n - 1) ≫
            (p.negOnePow⁻¹ • (columnXIso R A Q p (n - 1) (q - 1) _).hom)
        rw [ChainComplex.nativeShiftObjXIso'_d (coefficientComplex R A Q p)
          p n (n - 1) q (q - 1) h (by omega)]
        simp only [Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp,
          Iso.inv_hom_id, Category.comp_id, inv_smul_smul]) ≪≫
    ((coefficientComplex R A Q p).isoSc' (q + 1) q (q - 1)
      (down_prev q) (down_next q)).symm

private lemma columnScIso_hom_τ₂ (p n q : ℤ) (h : n - p = q) :
    (columnScIso R A Q p n q h).hom.τ₂ = (columnXIso R A Q p n q h).hom := by
  change (𝟙 _) ≫ (columnXIso R A Q p n q h).hom ≫ (𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

section Exact

variable [∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).PreservesHomology]

private def columnHomologyIso (p n q : ℤ) (h : n - p = q) :
    (zeroDifferentialTensorColumn R A Q p).homology n ≅
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).obj (Q.homology q) :=
  ShortComplex.homologyMapIso (columnScIso R A Q p n q h) ≪≫
    (HomologicalComplex.mapHomologyFunctorIso q
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p))).app Q

private def columnCyclesIso (p n q : ℤ) (h : n - p = q) :
    (zeroDifferentialTensorColumn R A Q p).cycles n ≅
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).obj (Q.cycles q) :=
  ShortComplex.cyclesMapIso (columnScIso R A Q p n q h) ≪≫
    (Q.sc q).mapCyclesIso ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p))

private lemma columnCyclesIso_hom_iCycles (p n q : ℤ) (h : n - p = q) :
    (columnCyclesIso R A Q p n q h).hom ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.iCycles q) =
      (zeroDifferentialTensorColumn R A Q p).iCycles n ≫
        (columnXIso R A Q p n q h).hom := by
  change ShortComplex.cyclesMap (columnScIso R A Q p n q h).hom ≫
      ((Q.sc q).mapCyclesIso _).hom ≫ _ = _
  rw [Category.assoc, ShortComplex.mapCyclesIso_hom_iCycles,
    ShortComplex.cyclesMap_i, columnScIso_hom_τ₂]

private lemma columnHomologyIso_hom_quotient (p n q : ℤ) (h : n - p = q) :
    (zeroDifferentialTensorColumn R A Q p).homologyπ n ≫
        (columnHomologyIso R A Q p n q h).hom =
      (columnCyclesIso R A Q p n q h).hom ≫
        ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.homologyπ q) := by
  change _ ≫ (ShortComplex.homologyMap (columnScIso R A Q p n q h).hom ≫
      ((Q.sc q).mapHomologyIso _).hom) = _
  rw [← Category.assoc, ShortComplex.homologyπ_naturality, Category.assoc,
    ShortComplex.homologyπ_comp_mapHomologyIso_hom]
  rfl

private lemma columnCyclesIso_inv_iCycles (p n q : ℤ) (h : n - p = q) :
    (columnCyclesIso R A Q p n q h).inv ≫
        (zeroDifferentialTensorColumn R A Q p).iCycles n =
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.iCycles q) ≫
        (columnXIso R A Q p n q h).inv := by
  apply (cancel_mono (columnXIso R A Q p n q h).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← columnCyclesIso_hom_iCycles]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private lemma columnHomologyIso_inv_quotient (p n q : ℤ) (h : n - p = q) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.homologyπ q) ≫
        (columnHomologyIso R A Q p n q h).inv =
      (columnCyclesIso R A Q p n q h).inv ≫
        (zeroDifferentialTensorColumn R A Q p).homologyπ n := by
  apply (cancel_mono (columnHomologyIso R A Q p n q h).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [columnHomologyIso_hom_quotient]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential.

For total degree n, the homology tensor family has term A_p⊗_R H_q(Q) for every integer pair p+q=n. -/
abbrev zeroDifferentialTensorHomologyFamily (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) :
    AddCommGrpCat.{v} :=
  ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A pq.val.1)).obj
    (Q.homology pq.val.2)

private def antidiagonalEquiv (n : ℤ) : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ≃ ℤ where
  toFun pq := pq.val.1
  invFun p := ⟨(p, n - p), by omega⟩
  left_inv pq := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change n - pq.val.1 = pq.val.2
      have h := pq.property
      omega
  right_inv _ := rfl

private def homologyAntidiagonalToColumnsIso (n : ℤ) :
    (∐ zeroDifferentialTensorHomologyFamily R A Q n) ≅
      colimit (zeroDifferentialTensorColumns R A Q ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} c n) :=
  HasColimit.isoOfEquivalence (Discrete.equivalence (antidiagonalEquiv n))
    (Discrete.natIso (fun pq =>
      columnHomologyIso R A Q pq.as.val.1 n pq.as.val.2 (by
        have h := pq.as.property
        omega)))

private lemma homologyAntidiagonalToColumnsIso_ι (p q n : ℤ) (h : p + q = n) :
    Sigma.ι (zeroDifferentialTensorHomologyFamily R A Q n) ⟨(p, q), h⟩ ≫
        (homologyAntidiagonalToColumnsIso R A Q n).hom =
      (columnHomologyIso R A Q p n q (by omega)).inv ≫
        colimit.ι (zeroDifferentialTensorColumns R A Q ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{v} c n) ⟨p⟩ := by
  simpa only [homologyAntidiagonalToColumnsIso, Discrete.natIso_inv_app,
    Discrete.equivalence_functor_obj, antidiagonalEquiv] using
      HasColimit.ι_isoOfEquivalence_hom
        (Discrete.equivalence (antidiagonalEquiv n))
        (Discrete.natIso (fun pq =>
          columnHomologyIso R A Q pq.as.val.1 n pq.as.val.2 (by
            have h := pq.as.property
            omega))) ⟨⟨(p, q), h⟩⟩

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential. Assume each coefficient functor A_p⊗_R− into abelian groups
preserves homology.

The canonical isomorphism ⊕_{p+q=n} A_p⊗_R H_q(Q) ≅ H_n(T(A,Q)). -/
@[no_expose]
def zeroDifferentialTensorHomologyIso (n : ℤ) :
    (∐ zeroDifferentialTensorHomologyFamily R A Q n) ≅
      (complex R (zeroDifferentialComplex R A) Q).homology n :=
  homologyAntidiagonalToColumnsIso R A Q n ≪≫
    (HomologicalComplex.homologyColimitIso (zeroDifferentialTensorColumns R A Q) n).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} c n).mapIso
        (zeroDifferentialTensorColumnsIso R A Q)

private lemma zeroDifferentialTensorHomologyIso_ι (p q n : ℤ) (h : p + q = n) :
    Sigma.ι (zeroDifferentialTensorHomologyFamily R A Q n) ⟨(p, q), h⟩ ≫
        (zeroDifferentialTensorHomologyIso R A Q n).hom =
      (columnHomologyIso R A Q p n q (by omega)).inv ≫
        HomologicalComplex.homologyMap (zeroDifferentialTensorColumnι R A Q p) n := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} c n
  have hcol : H.map (colimit.ι (zeroDifferentialTensorColumns R A Q) ⟨p⟩) ≫
      H.map (zeroDifferentialTensorColumnsIso R A Q).hom =
        H.map (zeroDifferentialTensorColumnι R A Q p) := by
    rw [← Functor.map_comp, ι_zeroDifferentialTensorColumnsIso_hom]
  have hanti := congrArg
    (fun f => f ≫
      (HomologicalComplex.homologyColimitIso (zeroDifferentialTensorColumns R A Q) n).inv ≫
      H.map (zeroDifferentialTensorColumnsIso R A Q).hom)
    (homologyAntidiagonalToColumnsIso_ι R A Q p q n h)
  change _ ≫ ((homologyAntidiagonalToColumnsIso R A Q n).hom ≫
      (HomologicalComplex.homologyColimitIso (zeroDifferentialTensorColumns R A Q) n).inv ≫
      H.map (zeroDifferentialTensorColumnsIso R A Q).hom) = _
  calc
    _ = (columnHomologyIso R A Q p n q (by omega)).inv ≫
        (colimit.ι (zeroDifferentialTensorColumns R A Q ⋙ H) ⟨p⟩ ≫
          (HomologicalComplex.homologyColimitIso (zeroDifferentialTensorColumns R A Q) n).inv) ≫
        H.map (zeroDifferentialTensorColumnsIso R A Q).hom := by
          simpa only [Category.assoc] using hanti
    _ = (columnHomologyIso R A Q p n q (by omega)).inv ≫
        H.map (colimit.ι (zeroDifferentialTensorColumns R A Q) ⟨p⟩) ≫
        H.map (zeroDifferentialTensorColumnsIso R A Q).hom := by
          rw [HomologicalComplex.ι_comp_homologyColimitIso_inv]
    _ = _ := congrArg (fun f => (columnHomologyIso R A Q p n q (by omega)).inv ≫ f) hcol

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential. Assume each coefficient functor A_p⊗_R− into abelian groups
preserves homology.

For p+q=n, the map A_p⊗_R Z_q(Q) → Z_n(T(A,Q)) whose cycle inclusion is the (p,q) total tensor-summand map applied to Q's cycle inclusion. -/
@[no_expose]
def zeroDifferentialTensorCyclesMap (p q n : ℤ) (h : p + q = n) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).obj (Q.cycles q) ⟶
      (complex R (zeroDifferentialComplex R A) Q).cycles n :=
  (columnCyclesIso R A Q p n q (by omega)).inv ≫
    HomologicalComplex.cyclesMap (zeroDifferentialTensorColumnι R A Q p) n

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential. Assume each coefficient functor A_p⊗_R− into abelian groups
preserves homology.

For p+q=n, including the image of A_p⊗_R Z_q(Q) into T(A,Q)_n equals the tensor of Q's cycle inclusion followed by the (p,q) total summand injection. -/
@[reassoc]
theorem zeroDifferentialTensorCyclesMap_iCycles (p q n : ℤ) (h : p + q = n) :
    zeroDifferentialTensorCyclesMap R A Q p q n h ≫
        (complex R (zeroDifferentialComplex R A) Q).iCycles n =
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.iCycles q) ≫
        HomologicalComplex.ιMapBifunctor (zeroDifferentialComplex R A) Q
          (ModuleCat.BalancedTensor.groupBifunctor R) c p q n h := by
  have hq : q = n - p := by omega
  subst q
  change
    ((columnCyclesIso R A Q p n (n - p) rfl).inv ≫
      HomologicalComplex.cyclesMap (zeroDifferentialTensorColumnι R A Q p) n) ≫
        (complex R (zeroDifferentialComplex R A) Q).iCycles n =
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.iCycles (n - p)) ≫
        tensorι R A Q p (n - p) n (by omega)
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    columnCyclesIso_inv_iCycles]
  change
    (((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.iCycles (n - p)) ≫
      (columnXIso R A Q p n (n - p) rfl).inv) ≫
        ((columnXIso R A Q p n (n - p) rfl).hom ≫
          tensorι R A Q p (n - p) n (by omega)) =
      ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.iCycles (n - p)) ≫
        tensorι R A Q p (n - p) n (by omega)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential. Assume each coefficient functor A_p⊗_R− into abelian groups
preserves homology.

For p+q=n, passing from A_p⊗_R Z_q(Q) through the homology projection of Q and the antidiagonal comparison equals its map to Z_n(T(A,Q)) followed by the total homology projection. -/
@[reassoc]
theorem zeroDifferentialTensorHomologyIso_cycle_class (p q n : ℤ) (h : p + q = n) :
    ((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.homologyπ q) ≫
        Sigma.ι (zeroDifferentialTensorHomologyFamily R A Q n) ⟨(p, q), h⟩ ≫
        (zeroDifferentialTensorHomologyIso R A Q n).hom =
      zeroDifferentialTensorCyclesMap R A Q p q n h ≫
        (complex R (zeroDifferentialComplex R A) Q).homologyπ n := by
  rw [zeroDifferentialTensorHomologyIso_ι,
    ← Category.assoc, columnHomologyIso_inv_quotient]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rfl

/-- Let R be an arbitrary ring, A=(A_p)_{p∈ℤ} a family of right R-modules
and Q an integer-indexed left-R-module chain complex.
Let T(A,Q)=Tot(A_0,Q), where A_0 has zero differential. Assume each coefficient functor A_p⊗_R− into abelian groups
preserves homology.

For p+q=n, x∈A_p and y∈Z_q(Q), there is a total cycle z whose underlying element is the (p,q) tensor x⊗y, and the homology comparison sends x⊗[y] to [z]. -/
theorem zeroDifferentialTensorHomologyIso_mk (p q n : ℤ) (h : p + q = n)
    (x : A p) (y : Q.cycles q) :
    letI : Module ℤ (Q.cycles q) := Module.compHom (Q.cycles q) (algebraMap ℤ R)
    letI : Module ℤ (Q.homology q) := Module.compHom (Q.homology q) (algebraMap ℤ R)
    ∃ z : (complex R (zeroDifferentialComplex R A) Q).cycles n,
      ((complex R (zeroDifferentialComplex R A) Q).iCycles n).hom z =
        mk R (zeroDifferentialComplex R A) Q p q n h x ((Q.iCycles q).hom y) ∧
      ((Sigma.ι (zeroDifferentialTensorHomologyFamily R A Q n) ⟨(p, q), h⟩ ≫
          (zeroDifferentialTensorHomologyIso R A Q n).hom).hom)
          (TensorProduct.Balanced.mk ℤ R (A p) (Q.homology q) x ((Q.homologyπ q).hom y)) =
        ((complex R (zeroDifferentialComplex R A) Q).homologyπ n).hom z := by
  letI : Module ℤ (Q.cycles q) := Module.compHom (Q.cycles q) (algebraMap ℤ R)
  letI : Module ℤ (Q.homology q) := Module.compHom (Q.homology q) (algebraMap ℤ R)
  let z := (zeroDifferentialTensorCyclesMap R A Q p q n h).hom
    (TensorProduct.Balanced.mk ℤ R (A p) (Q.cycles q) x y)
  refine ⟨z, ?_, ?_⟩
  · have hc := congrArg
      (fun f => f.hom (TensorProduct.Balanced.mk ℤ R (A p) (Q.cycles q) x y))
      (zeroDifferentialTensorCyclesMap_iCycles R A Q p q n h)
    change
      ((complex R (zeroDifferentialComplex R A) Q).iCycles n).hom
          ((zeroDifferentialTensorCyclesMap R A Q p q n h).hom
            (TensorProduct.Balanced.mk ℤ R (A p) (Q.cycles q) x y)) =
        (tensorι R A Q p q n h).hom
          ((((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.iCycles q)).hom
            (TensorProduct.Balanced.mk ℤ R (A p) (Q.cycles q) x y)) at hc
    erw [ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk] at hc
    exact hc
  · have hc := congrArg
      (fun f => f.hom (TensorProduct.Balanced.mk ℤ R (A p) (Q.cycles q) x y))
      (zeroDifferentialTensorHomologyIso_cycle_class R A Q p q n h)
    change
      ((Sigma.ι (zeroDifferentialTensorHomologyFamily R A Q n) ⟨(p, q), h⟩ ≫
          (zeroDifferentialTensorHomologyIso R A Q n).hom).hom)
          ((((ModuleCat.BalancedTensor.groupBifunctor R).obj (A p)).map (Q.homologyπ q)).hom
            (TensorProduct.Balanced.mk ℤ R (A p) (Q.cycles q) x y)) =
        ((complex R (zeroDifferentialComplex R A) Q).homologyπ n).hom
          ((zeroDifferentialTensorCyclesMap R A Q p q n h).hom
            (TensorProduct.Balanced.mk ℤ R (A p) (Q.cycles q) x y)) at hc
    erw [ModuleCat.BalancedTensor.groupBifunctor_obj_map_mk] at hc
    exact hc

end Exact

/-- Let R have universe u, A right-module carriers v and Q left-module
carriers w. At T=max(u,v,w,t), the full degree-n antidiagonal family
has term A_p^T⊗_R(H_q(Q))^T for p+q=n, lifting the original homology
object of Q. -/
def zeroDifferentialTensorHomologyFamilyAt
    (A : ℤ → ModuleCat.{v} Rᵐᵒᵖ) (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    (n : ℤ) (pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n}) :
    AddCommGrpCat.{max u v w t} :=
  ((ModuleCat.BalancedTensor.groupBifunctor R :
      ModuleCat.{max u v w t} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w t} R ⥤
        AddCommGrpCat.{max u v w t}).obj
      ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).obj (A pq.val.1))).obj
    ((ModuleCat.uliftFunctor.{max u v w t, w} R).obj (Q.homology pq.val.2))

/-- For an arbitrary ring R, a graded right-module family A and left-module
chain complex Q in independent worlds, the balanced tensor total at
T=max(u,v,w,t) of the lifted zero-differential family A^T and Q^T. -/
def zeroDifferentialTensorComplexAt
    (A : ℤ → ModuleCat.{v} Rᵐᵒᵖ) (Q : ChainComplex (ModuleCat.{w} R) ℤ) :
    ChainComplex AddCommGrpCat.{max u v w t} ℤ :=
  complex R
    (zeroDifferentialComplex R
      (fun p => (ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).obj (A p)))
    (((ModuleCat.uliftFunctor.{max u v w t, w} R).mapHomologicalComplex c).obj Q)

/-- Let R be arbitrary, A and Q have independent carrier universes, and
T=max(u,v,w,t). If each lifted coefficient functor A_p^T⊗_R− preserves
homology at T, the canonical comparison
⊕_{p+q=n} A_p^T⊗_R(H_q(Q))^T ≅ H_n(Tot(A_0^T,Q^T))
holds for every integer n. -/
def zeroDifferentialTensorHomologyIsoAt
    (A : ℤ → ModuleCat.{v} Rᵐᵒᵖ) (Q : ChainComplex (ModuleCat.{w} R) ℤ)
    [∀ p : ℤ, ((ModuleCat.BalancedTensor.groupBifunctor R :
        ModuleCat.{max u v w t} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w t} R ⥤
          AddCommGrpCat.{max u v w t}).obj
        ((ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).obj (A p))).PreservesHomology]
    (n : ℤ) :
    (∐ zeroDifferentialTensorHomologyFamilyAt.{u, v, w, t} R A Q n) ≅
      (zeroDifferentialTensorComplexAt.{u, v, w, t} R A Q).homology n := by
  let AL : ℤ → ModuleCat.{max u v w t} Rᵐᵒᵖ :=
    fun p => (ModuleCat.uliftFunctor.{max u v w t, v} Rᵐᵒᵖ).obj (A p)
  let L : ModuleCat.{w} R ⥤ ModuleCat.{max u v w t} R :=
    ModuleCat.uliftFunctor.{max u v w t, w} R
  let QL : ChainComplex (ModuleCat.{max u v w t} R) ℤ :=
    (L.mapHomologicalComplex c).obj Q
  let F : ModuleCat.{max u v w t} Rᵐᵒᵖ ⥤ ModuleCat.{max u v w t} R ⥤
      AddCommGrpCat.{max u v w t} := ModuleCat.BalancedTensor.groupBifunctor R
  letI : ∀ p : ℤ, (F.obj (AL p)).PreservesHomology := fun p => inferInstance
  let e : Discrete.functor (zeroDifferentialTensorHomologyFamilyAt.{u, v, w, t} R A Q n) ≅
      Discrete.functor (zeroDifferentialTensorHomologyFamily R AL QL n) :=
    Discrete.natIso (fun pq =>
      (F.obj (AL pq.as.val.1)).mapIso
        ((HomologicalComplex.mapHomologyFunctorIso pq.as.val.2 L).app Q).symm)
  exact (colim (J := Discrete {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (C := AddCommGrpCat.{max u v w t})).mapIso e ≪≫
      zeroDifferentialTensorHomologyIso R AL QL n

end ChainComplex.BalancedTensor
