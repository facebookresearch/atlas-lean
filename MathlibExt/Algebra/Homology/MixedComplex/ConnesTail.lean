/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.MixedComplex.ConnesConstruction
public import MathlibExt.Algebra.Homology.PartialTotalEvenTail

/-!
# The two-degree tail of a mixed Connes complex

The surviving cell in bidegree (p + 1, q + 1) is identified with the
original cell (p, q). The signed-column differential and the vertical
totalization sign cancel. Total coprojections and the first-column
cokernel give the tail comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace MixedComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] (M : MixedComplex C)
  [M.connesBicomplex.HasTotal (ComplexShape.down ℕ)]

local notation "c" => ComplexShape.down ℕ

/-- The total summand with column p and underlying mixed degree n. -/
def connesSummandι (p n q j : ℕ) (hn : n + p = q) (hj : p + q = j) :
    M.underlying.X n ⟶ (M.connesBicomplex.total c).X j :=
  (ChainComplex.mixedColumnIso M.underlying p n q hn).inv ≫
    M.connesBicomplex.ιTotal c p q j hj

/-- The positive-column horizontal total differential is the original B map. -/
@[reassoc]
theorem connesSummandι_D₁ (p n q j j' : ℕ)
    (hn : n + (p + 1) = q) (hj : (p + 1) + q = j) (hj' : p + q = j') :
    M.connesSummandι (p + 1) n q j hn hj ≫ M.connesBicomplex.D₁ c j j' =
      M.B n ≫ M.connesSummandι p (n + 1) q j' (by omega) hj' := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let e : (B.X (p + 1)).X q ≅ M.underlying.X n :=
    ChainComplex.mixedColumnIso M.underlying (p + 1) n q hn
  let e' : (B.X p).X q ≅ M.underlying.X (n + 1) :=
    ChainComplex.mixedColumnIso M.underlying p (n + 1) q (by omega)
  let ι : (B.X (p + 1)).X q ⟶ T.X j := B.ιTotal c (p + 1) q j hj
  let ι' : (B.X p).X q ⟶ T.X j' := B.ιTotal c p q j' hj'
  have hε : ComplexShape.ε₁ c c c (p + 1, q) = 1 := rfl
  have hHorizontal : (B.d (p + 1) p).f q =
      ChainComplex.mixedHorizontalComponent M.underlying M.boundaryHomotopy p q := by
    dsimp only [B, connesBicomplex, ChainComplex.mixedBicomplex]
    rw [ChainComplex.of_d, ChainComplex.mixedHorizontalMap_f]
  have hB : (B.d (p + 1) p).f q = e.hom ≫ M.B n ≫ e'.inv :=
    (hHorizontal.trans (ChainComplex.mixedHorizontalComponent_eq
      M.underlying M.boundaryHomotopy p n q hn)).trans
        (congrArg (fun f : M.underlying.X n ⟶ M.underlying.X (n + 1) =>
          e.hom ≫ f ≫ e'.inv) (M.boundaryHomotopy_hom n))
  have hι : ι ≫ B.D₁ c j j' = (B.d (p + 1) p).f q ≫ ι' := by
    have h := (B.ι_D₁ c j j' (p + 1) q hj).trans
      (B.d₁_eq c (by rfl : (c).Rel (p + 1) p) q j' hj')
    simpa only [hε, one_smul] using h
  change (e.inv ≫ ι) ≫ B.D₁ c j j' = M.B n ≫ e'.inv ≫ ι'
  calc
    _ = e.inv ≫ (ι ≫ B.D₁ c j j') := Category.assoc _ _ _
    _ = e.inv ≫ ((B.d (p + 1) p).f q ≫ ι') :=
      congrArg (fun f : (B.X (p + 1)).X q ⟶ T.X j' => e.inv ≫ f) hι
    _ = e.inv ≫ ((e.hom ≫ M.B n ≫ e'.inv) ≫ ι') :=
      congrArg (fun f : (B.X (p + 1)).X q ⟶ (B.X p).X q => e.inv ≫ f ≫ ι') hB
    _ = M.B n ≫ e'.inv ≫ ι' := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Column zero has no outgoing horizontal total differential. -/
@[reassoc]
theorem connesSummandι_D₁_zero (n q j j' : ℕ) (hn : n + 0 = q) (hj : 0 + q = j) :
    M.connesSummandι 0 n q j hn hj ≫ M.connesBicomplex.D₁ c j j' = 0 := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let e : (B.X 0).X q ≅ M.underlying.X n :=
    ChainComplex.mixedColumnIso M.underlying 0 n q hn
  let ι : (B.X 0).X q ⟶ T.X j := B.ιTotal c 0 q j hj
  have hι : ι ≫ B.D₁ c j j' = 0 :=
    (B.ι_D₁ c j j' 0 q hj).trans
      (B.d₁_eq_zero c 0 q j' (by change ¬ ((c).next 0 + 1 = 0); omega))
  change (e.inv ≫ ι) ≫ B.D₁ c j j' = 0
  calc
    _ = e.inv ≫ (ι ≫ B.D₁ c j j') := Category.assoc _ _ _
    _ = e.inv ≫ 0 := congrArg (fun f : (B.X 0).X q ⟶ T.X j' => e.inv ≫ f) hι
    _ = 0 := comp_zero

/-- The native vertical total sign cancels the column sign, leaving positive b. -/
@[reassoc]
theorem connesSummandι_D₂ (p n q q' j j' : ℕ)
    (hn : (n + 1) + p = q) (hn' : n + p = q')
    (hj : p + q = j) (hj' : p + q' = j') :
    M.connesSummandι p (n + 1) q j hn hj ≫ M.connesBicomplex.D₂ c j j' =
      M.underlying.d (n + 1) n ≫ M.connesSummandι p n q' j' hn' hj' := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let e : (B.X p).X q ≅ M.underlying.X (n + 1) :=
    ChainComplex.mixedColumnIso M.underlying p (n + 1) q hn
  let e' : (B.X p).X q' ≅ M.underlying.X n :=
    ChainComplex.mixedColumnIso M.underlying p n q' hn'
  let ι : (B.X p).X q ⟶ T.X j := B.ιTotal c p q j hj
  let ι' : (B.X p).X q' ⟶ T.X j' := B.ιTotal c p q' j' hj'
  have hε : ComplexShape.ε₂ c c c (p, q) = (c).ε p := rfl
  have hD : (c).ε p • (B.X p).d q q' = e.hom ≫ M.underlying.d (n + 1) n ≫ e'.inv :=
    ChainComplex.mixedBicomplex_total_vertical M.underlying M.boundaryHomotopy
      (fun n => by simpa only [boundaryHomotopy_hom] using M.B_sq n)
      p (n + 1) n q q' hn hn'
  have hι : ι ≫ B.D₂ c j j' = ((c).ε p • (B.X p).d q q') ≫ ι' := by
    have h := (B.ι_D₂ c j j' p q hj).trans
      (B.d₂_eq c p (by change q' + 1 = q; omega) j' hj')
    simpa only [hε, ← Linear.units_smul_comp] using h
  change (e.inv ≫ ι) ≫ B.D₂ c j j' = M.underlying.d (n + 1) n ≫ e'.inv ≫ ι'
  calc
    _ = e.inv ≫ (ι ≫ B.D₂ c j j') := Category.assoc _ _ _
    _ = e.inv ≫ (((c).ε p • (B.X p).d q q') ≫ ι') :=
      congrArg (fun f : (B.X p).X q ⟶ T.X j' => e.inv ≫ f) hι
    _ = e.inv ≫ ((e.hom ≫ M.underlying.d (n + 1) n ≫ e'.inv) ≫ ι') :=
      congrArg (fun f : (B.X p).X q ⟶ (B.X p).X q' => e.inv ≫ f ≫ ι') hD
    _ = M.underlying.d (n + 1) n ≫ e'.inv ≫ ι' := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The vertical differential at underlying mixed degree zero lands outside the support. -/
@[reassoc]
theorem connesSummandι_D₂_zero (p q j j' : ℕ) (hn : 0 + p = q) (hj : p + q = j) :
    M.connesSummandι p 0 q j hn hj ≫ M.connesBicomplex.D₂ c j j' = 0 := by
  have hD : M.connesBicomplex.d₂ c p q j' = 0 := by
    cases q with
    | zero =>
        exact M.connesBicomplex.d₂_eq_zero c p 0 j'
          (by change ¬ ((c).next 0 + 1 = 0); omega)
    | succ q =>
        have hp : p = q + 1 := by omega
        subst p
        have hz := M.connesBicomplex_isZero_cell (q + 1) q (by omega)
        have hd : (M.connesBicomplex.X (q + 1)).d (q + 1) q = 0 := hz.eq_of_tgt _ _
        rw [M.connesBicomplex.d₂_eq' c (q + 1)
          (by rfl : (c).Rel (q + 1) q) j', hd, zero_comp, smul_zero]
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let e : (B.X p).X q ≅ M.underlying.X 0 :=
    ChainComplex.mixedColumnIso M.underlying p 0 q hn
  let ι : (B.X p).X q ⟶ T.X j := B.ιTotal c p q j hj
  have hι : ι ≫ B.D₂ c j j' = 0 := (B.ι_D₂ c j j' p q hj).trans hD
  change (e.inv ≫ ι) ≫ B.D₂ c j j' = 0
  calc
    _ = e.inv ≫ (ι ≫ B.D₂ c j j') := Category.assoc _ _ _
    _ = e.inv ≫ 0 := congrArg (fun f : (B.X p).X q ⟶ T.X j' => e.inv ≫ f) hι
    _ = 0 := comp_zero

/-- In column zero the total differential is the original chain differential. -/
@[reassoc]
theorem connesSummandι_d_zero_column (n q q' j j' : ℕ)
    (hn : (n + 1) + 0 = q) (hn' : n + 0 = q')
    (hj : 0 + q = j) (hj' : 0 + q' = j') :
    M.connesSummandι 0 (n + 1) q j hn hj ≫ (M.connesBicomplex.total c).d j j' =
      M.underlying.d (n + 1) n ≫ M.connesSummandι 0 n q' j' hn' hj' := by
  change M.connesSummandι 0 (n + 1) q j hn hj ≫
    (M.connesBicomplex.D₁ c j j' + M.connesBicomplex.D₂ c j j') = _
  rw [Preadditive.comp_add, M.connesSummandι_D₁_zero,
    M.connesSummandι_D₂ 0 n q q' j j' hn hn' hj hj', zero_add]

/-- At mixed degree zero, only the original B term survives in a positive column. -/
@[reassoc]
theorem connesSummandι_d_zero_degree (p q j j' : ℕ)
    (hn : 0 + (p + 1) = q) (hj : (p + 1) + q = j) (hj' : p + q = j') :
    M.connesSummandι (p + 1) 0 q j hn hj ≫ (M.connesBicomplex.total c).d j j' =
      M.B 0 ≫ M.connesSummandι p 1 q j' (by omega) hj' := by
  change M.connesSummandι (p + 1) 0 q j hn hj ≫
    (M.connesBicomplex.D₁ c j j' + M.connesBicomplex.D₂ c j j') = _
  rw [Preadditive.comp_add, M.connesSummandι_D₁ p 0 q j j' hn hj hj',
    M.connesSummandι_D₂_zero, add_zero]

/-- Positive mixed degree in a positive column has exactly the original B and b terms. -/
@[reassoc]
theorem connesSummandι_d (p n q j j' : ℕ)
    (hn : (n + 1) + (p + 1) = q) (hj : (p + 1) + q = j) (hj' : p + q = j') :
    M.connesSummandι (p + 1) (n + 1) q j hn hj ≫
        (M.connesBicomplex.total c).d j j' =
      M.B (n + 1) ≫ M.connesSummandι p (n + 2) q j' (by omega) hj' +
        M.underlying.d (n + 1) n ≫
          M.connesSummandι (p + 1) n (q - 1) j' (by omega) (by omega) := by
  change M.connesSummandι (p + 1) (n + 1) q j hn hj ≫
    (M.connesBicomplex.D₁ c j j' + M.connesBicomplex.D₂ c j j') = _
  rw [Preadditive.comp_add, M.connesSummandι_D₁ p (n + 1) q j j' hn hj hj',
    M.connesSummandι_D₂ (p + 1) n q (q - 1) j j' hn (by omega) hj (by omega)]

/-- The original periodicity component discards column zero and moves each surviving
cell one place in both directions. The target is the zero extension. -/
def connesPeriodicityF (j : ℕ) :
    (M.connesBicomplex.total c).X j ⟶
      ((M.connesBicomplex.total c).extend
        (ComplexShape.embeddingDown'Add (1 : ℕ) 2)).X j :=
  M.connesBicomplex.totalDesc fun p q hj =>
    match p with
    | 0 => 0
    | p + 1 =>
        if hpq : p + 1 ≤ q then
          (ChainComplex.mixedColumnIso M.underlying (p + 1)
            (q - (p + 1)) q (Nat.sub_add_cancel hpq)).hom ≫
              M.connesSummandι p (q - (p + 1)) (q - 1) (j - 2)
                (by omega) (by change (p + 1) + q = j at hj; omega) ≫
                  ((M.connesBicomplex.total c).extendXIso
                    (ComplexShape.embeddingDown'Add (1 : ℕ) 2)
                    (show j - 2 + 2 = j from by
                      change (p + 1) + q = j at hj
                      omega)).inv
        else 0

/-- The periodicity component kills the original zeroth column. -/
@[reassoc]
theorem connesSummandι_periodicityF_zero (n q j : ℕ) (hn : n + 0 = q) (hj : 0 + q = j) :
    M.connesSummandι 0 n q j hn hj ≫ M.connesPeriodicityF j = 0 := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let S : ChainComplex C ℕ := T.extend E
  let e : (B.X 0).X q ≅ M.underlying.X n :=
    ChainComplex.mixedColumnIso M.underlying 0 n q hn
  let ι : (B.X 0).X q ⟶ T.X j := B.ιTotal c 0 q j hj
  let π : T.X j ⟶ S.X j := M.connesPeriodicityF j
  have hι : ι ≫ π = 0 := by
    change B.ιTotal c 0 q j hj ≫ B.totalDesc (A := S.X j) _ = 0
    exact B.ι_totalDesc (f := _) 0 q hj
  change (e.inv ≫ ι) ≫ π = 0
  calc
    _ = e.inv ≫ (ι ≫ π) := Category.assoc _ _ _
    _ = e.inv ≫ 0 := congrArg (fun f : (B.X 0).X q ⟶ S.X j => e.inv ≫ f) hι
    _ = 0 := comp_zero

/-- A positive-column periodicity component preserves the original mixed-degree summand. -/
@[reassoc]
theorem connesSummandι_periodicityF (p n q j k : ℕ)
    (hn : n + (p + 1) = q) (hj : (p + 1) + q = j) (hk : k + 2 = j) :
    M.connesSummandι (p + 1) n q j hn hj ≫ M.connesPeriodicityF j ≫
        ((M.connesBicomplex.total c).extendXIso
          (ComplexShape.embeddingDown'Add (1 : ℕ) 2) hk).hom =
      M.connesSummandι p n (q - 1) k (by omega) (by omega) := by
  have hpq : p + 1 ≤ q := by omega
  obtain rfl : n = q - (p + 1) := by omega
  obtain rfl : k = j - 2 := by omega
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let S : ChainComplex C ℕ := T.extend E
  let e : (B.X (p + 1)).X q ≅ M.underlying.X (q - (p + 1)) :=
    ChainComplex.mixedColumnIso M.underlying (p + 1) (q - (p + 1)) q hn
  let a : S.X j ≅ T.X (j - 2) := T.extendXIso E hk
  let ι : (B.X (p + 1)).X q ⟶ T.X j := B.ιTotal c (p + 1) q j hj
  let κ : M.underlying.X (q - (p + 1)) ⟶ T.X (j - 2) :=
    M.connesSummandι p (q - (p + 1)) (q - 1) (j - 2) (by omega) (by omega)
  let π : T.X j ⟶ S.X j := M.connesPeriodicityF j
  have hι : ι ≫ π = e.hom ≫ κ ≫ a.inv := by
    change B.ιTotal c (p + 1) q j hj ≫ B.totalDesc (A := S.X j) _ = _
    refine (B.ι_totalDesc (f := _) (p + 1) q hj).trans ?_
    exact dite_eq_left hpq
  change (e.inv ≫ ι) ≫ π ≫ a.hom = κ
  calc
    _ = e.inv ≫ ((ι ≫ π) ≫ a.hom) := by simp only [Category.assoc]
    _ = e.inv ≫ ((e.hom ≫ κ ≫ a.inv) ≫ a.hom) :=
      congrArg (fun f : (B.X (p + 1)).X q ⟶ S.X j => e.inv ≫ f ≫ a.hom) hι
    _ = κ := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- On each actual mixed summand, periodicity commutes with both original differential terms. -/
theorem connesSummandι_periodicityF_comm (p r q n k : ℕ)
    (hr : r + p = q) (hq : p + q = n + 1) (hk : k + 2 = n) :
    M.connesSummandι p r q (n + 1) hr hq ≫ M.connesPeriodicityF (n + 1) ≫
        ((M.connesBicomplex.total c).extendXIso
          (ComplexShape.embeddingDown'Add (1 : ℕ) 2)
          (show (k + 1) + 2 = n + 1 from by omega)).hom ≫
            (M.connesBicomplex.total c).d (k + 1) k =
      M.connesSummandι p r q (n + 1) hr hq ≫ (M.connesBicomplex.total c).d (n + 1) n ≫
        M.connesPeriodicityF n ≫
          ((M.connesBicomplex.total c).extendXIso
            (ComplexShape.embeddingDown'Add (1 : ℕ) 2) hk).hom := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let S : ChainComplex C ℕ := T.extend E
  let b : S.X n ≅ T.X k := T.extendXIso E hk
  cases p with
  | zero =>
      have hq' : q = n + 1 := by omega
      have hr' : r = n + 1 := by omega
      subst q
      subst r
      have hd := M.connesSummandι_d_zero_column n (n + 1) n (n + 1) n rfl rfl
        (Nat.zero_add (n + 1)) (Nat.zero_add n)
      calc
        _ = 0 := by rw [M.connesSummandι_periodicityF_zero_assoc, zero_comp]
        _ = (M.connesSummandι 0 (n + 1) (n + 1) (n + 1) rfl (Nat.zero_add (n + 1)) ≫
            T.d (n + 1) n) ≫ (M.connesPeriodicityF n ≫ b.hom) := by
           let π : T.X n ⟶ S.X n := M.connesPeriodicityF n
           let ρ : T.X n ⟶ T.X k := π ≫ b.hom
           let i : M.underlying.X n ⟶ T.X n :=
             M.connesSummandι 0 n n n rfl (Nat.zero_add n)
           have hz : i ≫ π = 0 := M.connesSummandι_periodicityF_zero n n n rfl (Nat.zero_add n)
           have hi : i ≫ ρ = 0 :=
             (Category.assoc i π b.hom).symm.trans
               ((congrArg (fun f : M.underlying.X n ⟶ S.X n => f ≫ b.hom) hz).trans
                 (zero_comp))
           have hd' : M.connesSummandι 0 (n + 1) (n + 1) (n + 1) rfl
               (Nat.zero_add (n + 1)) ≫ T.d (n + 1) n = M.underlying.d (n + 1) n ≫ i := hd
           have h : (M.connesSummandι 0 (n + 1) (n + 1) (n + 1) rfl
               (Nat.zero_add (n + 1)) ≫ T.d (n + 1) n) ≫ ρ = 0 := by
             calc
               _ = (M.underlying.d (n + 1) n ≫ i) ≫ ρ :=
                 congrArg (fun f : M.underlying.X (n + 1) ⟶ T.X n => f ≫ ρ) hd'
               _ = M.underlying.d (n + 1) n ≫ (i ≫ ρ) := Category.assoc _ _ _
               _ = M.underlying.d (n + 1) n ≫ (0 : M.underlying.X n ⟶ T.X k) :=
                 congrArg (fun f : M.underlying.X n ⟶ T.X k => M.underlying.d (n + 1) n ≫ f) hi
               _ = 0 := comp_zero
           exact h.symm
        _ = _ := Category.assoc _ _ _
  | succ p =>
      cases r with
      | zero =>
          cases p with
          | zero => omega
          | succ p =>
              have hds := M.connesSummandι_d_zero_degree (p + 1) q (n + 1) n hr hq (by omega)
              have hdt := M.connesSummandι_d_zero_degree p (q - 1) (k + 1) k
                (by omega) (by omega) (by omega)
              calc
                _ = M.connesSummandι (p + 1) 0 (q - 1) (k + 1) (by omega) (by omega) ≫
                    T.d (k + 1) k := by
                  rw [M.connesSummandι_periodicityF_assoc]
                _ = M.B 0 ≫ M.connesSummandι p 1 (q - 1) k (by omega) (by omega) := hdt
                _ = (M.connesSummandι (p + 2) 0 q (n + 1) hr hq ≫
                    T.d (n + 1) n) ≫ (M.connesPeriodicityF n ≫ b.hom) := by
                   let π : T.X n ⟶ S.X n := M.connesPeriodicityF n
                   let ρ : T.X n ⟶ T.X k := π ≫ b.hom
                   let i : M.underlying.X 1 ⟶ T.X n :=
                     M.connesSummandι (p + 1) 1 q n (by omega) (by omega)
                   let j : M.underlying.X 1 ⟶ T.X k :=
                     M.connesSummandι p 1 (q - 1) k (by omega) (by omega)
                   have hi : i ≫ ρ = j :=
                     M.connesSummandι_periodicityF p 1 q n k (by omega) (by omega) hk
                   have hd' : M.connesSummandι (p + 2) 0 q (n + 1) hr hq ≫
                       T.d (n + 1) n = M.B 0 ≫ i := hds
                   have h : (M.connesSummandι (p + 2) 0 q (n + 1) hr hq ≫
                       T.d (n + 1) n) ≫ ρ = M.B 0 ≫ j := by
                     calc
                       _ = (M.B 0 ≫ i) ≫ ρ :=
                         congrArg (fun f : M.underlying.X 0 ⟶ T.X n => f ≫ ρ) hd'
                       _ = M.B 0 ≫ (i ≫ ρ) := Category.assoc _ _ _
                       _ = M.B 0 ≫ j :=
                         congrArg (fun f : M.underlying.X 1 ⟶ T.X k => M.B 0 ≫ f) hi
                   exact h.symm
                _ = _ := Category.assoc _ _ _
      | succ r =>
          have hds := M.connesSummandι_d p r q (n + 1) n hr hq (by omega)
          cases p with
          | zero =>
              have hdt := M.connesSummandι_d_zero_column r (q - 1) (q - 2) (k + 1) k
                (by omega) (by omega) (by omega) (by omega)
              calc
                _ = M.connesSummandι 0 (r + 1) (q - 1) (k + 1) (by omega) (by omega) ≫
                    T.d (k + 1) k := by
                  rw [M.connesSummandι_periodicityF_assoc]
                _ = M.underlying.d (r + 1) r ≫
                    M.connesSummandι 0 r (q - 2) k (by omega) (by omega) := hdt
                _ = (M.connesSummandι 1 (r + 1) q (n + 1) hr hq ≫
                    T.d (n + 1) n) ≫ (M.connesPeriodicityF n ≫ b.hom) := by
                   let ρ : T.X n ⟶ T.X k := M.connesPeriodicityF n ≫ b.hom
                   let i₀ : M.underlying.X (r + 2) ⟶ T.X n :=
                     M.connesSummandι 0 (r + 2) q n (by omega) (by omega)
                   let i₁ : M.underlying.X r ⟶ T.X n :=
                     M.connesSummandι 1 r (q - 1) n (by omega) (by omega)
                   let i₂ : M.underlying.X r ⟶ T.X k :=
                     M.connesSummandι 0 r (q - 2) k (by omega) (by omega)
                   have hz : i₀ ≫ ρ = 0 := by
                     let π : T.X n ⟶ S.X n := M.connesPeriodicityF n
                     have h : i₀ ≫ M.connesPeriodicityF n = 0 :=
                       M.connesSummandι_periodicityF_zero (r + 2) q n (by omega) (by omega)
                     exact (Category.assoc i₀ π b.hom).symm.trans
                       ((congrArg (fun f : M.underlying.X (r + 2) ⟶ S.X n => f ≫ b.hom) h).trans
                         (zero_comp))
                   have h₁ : i₁ ≫ ρ = i₂ := by
                     have h : i₁ ≫ ρ =
                         M.connesSummandι 0 r (q - 1 - 1) k (by omega) (by omega) :=
                       M.connesSummandι_periodicityF 0 r (q - 1) n k (by omega) (by omega) hk
                     simpa only [Nat.sub_sub] using h
                   have hs : M.connesSummandι 1 (r + 1) q (n + 1) hr hq ≫
                       T.d (n + 1) n = M.B (r + 1) ≫ i₀ + M.underlying.d (r + 1) r ≫ i₁ := hds
                   have h : (M.connesSummandι 1 (r + 1) q (n + 1) hr hq ≫
                       T.d (n + 1) n) ≫ ρ = M.underlying.d (r + 1) r ≫ i₂ := by
                     calc
                       _ = (M.B (r + 1) ≫ i₀ + M.underlying.d (r + 1) r ≫ i₁) ≫ ρ :=
                         congrArg (fun f : M.underlying.X (r + 1) ⟶ T.X n => f ≫ ρ) hs
                       _ = (M.B (r + 1) ≫ i₀) ≫ ρ +
                            (M.underlying.d (r + 1) r ≫ i₁) ≫ ρ :=
                          Preadditive.add_comp (M.underlying.X (r + 1)) (T.X n) (T.X k)
                            (M.B (r + 1) ≫ i₀) (M.underlying.d (r + 1) r ≫ i₁) ρ
                       _ = M.B (r + 1) ≫ (i₀ ≫ ρ) +
                           M.underlying.d (r + 1) r ≫ (i₁ ≫ ρ) :=
                         congrArg₂ (fun f g : M.underlying.X (r + 1) ⟶ T.X k => f + g)
                           (Category.assoc _ _ _) (Category.assoc _ _ _)
                       _ = M.B (r + 1) ≫ 0 + M.underlying.d (r + 1) r ≫ i₂ :=
                         congrArg₂ (fun f g : M.underlying.X (r + 1) ⟶ T.X k => f + g)
                           (congrArg (fun f : M.underlying.X (r + 2) ⟶ T.X k =>
                             M.B (r + 1) ≫ f) hz)
                           (congrArg (fun f : M.underlying.X r ⟶ T.X k =>
                             M.underlying.d (r + 1) r ≫ f) h₁)
                       _ = M.underlying.d (r + 1) r ≫ i₂ :=
                         (congrArg (fun f : M.underlying.X (r + 1) ⟶ T.X k =>
                           f + M.underlying.d (r + 1) r ≫ i₂)
                           (comp_zero : M.B (r + 1) ≫ (0 : M.underlying.X (r + 2) ⟶ T.X k) = 0)).trans
                             (zero_add (M.underlying.d (r + 1) r ≫ i₂))
                   exact h.symm
                _ = _ := Category.assoc _ _ _
          | succ p =>
              have hdt := M.connesSummandι_d p r (q - 1) (k + 1) k
                (by omega) (by omega) (by omega)
              calc
                _ = M.connesSummandι (p + 1) (r + 1) (q - 1) (k + 1) (by omega) (by omega) ≫
                    T.d (k + 1) k := by
                  rw [M.connesSummandι_periodicityF_assoc]
                _ = M.B (r + 1) ≫ M.connesSummandι p (r + 2) (q - 1) k (by omega) (by omega) +
                    M.underlying.d (r + 1) r ≫
                      M.connesSummandι (p + 1) r (q - 2) k (by omega) (by omega) := by
                  simpa only [Nat.sub_sub] using hdt
                _ = (M.connesSummandι (p + 2) (r + 1) q (n + 1) hr hq ≫
                    T.d (n + 1) n) ≫ (M.connesPeriodicityF n ≫ b.hom) := by
                   let π : T.X n ⟶ S.X n := M.connesPeriodicityF n
                   let ρ : T.X n ⟶ T.X k := π ≫ b.hom
                   let i₀ : M.underlying.X (r + 2) ⟶ T.X n :=
                     M.connesSummandι (p + 1) (r + 2) q n (by omega) (by omega)
                   let i₁ : M.underlying.X r ⟶ T.X n :=
                     M.connesSummandι (p + 2) r (q - 1) n (by omega) (by omega)
                   let j₀ : M.underlying.X (r + 2) ⟶ T.X k :=
                     M.connesSummandι p (r + 2) (q - 1) k (by omega) (by omega)
                   let j₁ : M.underlying.X r ⟶ T.X k :=
                     M.connesSummandι (p + 1) r (q - 2) k (by omega) (by omega)
                   have h₀ : i₀ ≫ ρ = j₀ :=
                     M.connesSummandι_periodicityF p (r + 2) q n k (by omega) (by omega) hk
                   have h₁ : i₁ ≫ ρ = j₁ := by
                     have h : i₁ ≫ ρ = M.connesSummandι (p + 1) r (q - 1 - 1) k
                         (by omega) (by omega) :=
                       M.connesSummandι_periodicityF (p + 1) r (q - 1) n k (by omega) (by omega) hk
                     simpa only [Nat.sub_sub] using h
                   have hd' : M.connesSummandι (p + 2) (r + 1) q (n + 1) hr hq ≫
                       T.d (n + 1) n = M.B (r + 1) ≫ i₀ + M.underlying.d (r + 1) r ≫ i₁ := hds
                   have h : (M.connesSummandι (p + 2) (r + 1) q (n + 1) hr hq ≫
                       T.d (n + 1) n) ≫ ρ = M.B (r + 1) ≫ j₀ + M.underlying.d (r + 1) r ≫ j₁ := by
                     calc
                       _ = (M.B (r + 1) ≫ i₀ + M.underlying.d (r + 1) r ≫ i₁) ≫ ρ :=
                         congrArg (fun f : M.underlying.X (r + 1) ⟶ T.X n => f ≫ ρ) hd'
                       _ = (M.B (r + 1) ≫ i₀) ≫ ρ +
                           (M.underlying.d (r + 1) r ≫ i₁) ≫ ρ :=
                         Preadditive.add_comp (M.underlying.X (r + 1)) (T.X n) (T.X k)
                           (M.B (r + 1) ≫ i₀) (M.underlying.d (r + 1) r ≫ i₁) ρ
                       _ = M.B (r + 1) ≫ (i₀ ≫ ρ) + M.underlying.d (r + 1) r ≫ (i₁ ≫ ρ) :=
                         congrArg₂ (fun f g : M.underlying.X (r + 1) ⟶ T.X k => f + g)
                           (Category.assoc _ _ _) (Category.assoc _ _ _)
                       _ = M.B (r + 1) ≫ j₀ + M.underlying.d (r + 1) r ≫ j₁ :=
                         congrArg₂ (fun f g : M.underlying.X (r + 1) ⟶ T.X k => f + g)
                           (congrArg (fun f : M.underlying.X (r + 2) ⟶ T.X k => M.B (r + 1) ≫ f) h₀)
                           (congrArg (fun f : M.underlying.X r ⟶ T.X k => M.underlying.d (r + 1) r ≫ f) h₁)
                   exact h.symm
                _ = _ := Category.assoc _ _ _

/-- The computed periodicity components assemble into a chain map. -/
theorem connesPeriodicityF_comm (n : ℕ) :
    M.connesPeriodicityF (n + 1) ≫
        ((M.connesBicomplex.total c).extend
          (ComplexShape.embeddingDown'Add (1 : ℕ) 2)).d (n + 1) n =
      (M.connesBicomplex.total c).d (n + 1) n ≫ M.connesPeriodicityF n := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  by_cases hn : 2 ≤ n
  · let k := n - 2
    have hk : k + 2 = n := Nat.sub_add_cancel hn
    let S : ChainComplex C ℕ := T.extend E
    let a : S.X (n + 1) ≅ T.X (k + 1) :=
      T.extendXIso E (show (k + 1) + 2 = n + 1 from by omega)
    let b : S.X n ≅ T.X k := T.extendXIso E hk
    let F : T.X (n + 1) ⟶ S.X (n + 1) := M.connesPeriodicityF (n + 1)
    let F' : T.X n ⟶ S.X n := M.connesPeriodicityF n
    have hd : S.d (n + 1) n = a.hom ≫ T.d (k + 1) k ≫ b.inv :=
      T.extend_d_eq E (show (k + 1) + 2 = n + 1 from by omega) hk
    change F ≫ S.d (n + 1) n = T.d (n + 1) n ≫ F'
    have hComp : F ≫ a.hom ≫ T.d (k + 1) k = T.d (n + 1) n ≫ F' ≫ b.hom := by
      apply HomologicalComplex₂.total.hom_ext
      intro p q hpq
      by_cases hs : p ≤ q
      · obtain ⟨r, rfl⟩ : ∃ r, q = r + p := ⟨q - p, (Nat.sub_add_cancel hs).symm⟩
        let e : (B.X p).X (r + p) ≅ M.underlying.X r :=
          ChainComplex.mixedColumnIso M.underlying p r (r + p) rfl
        let ι : (B.X p).X (r + p) ⟶ T.X (n + 1) := B.ιTotal c p (r + p) (n + 1) hpq
        let π : T.X (n + 1) ⟶ S.X (n + 1) := M.connesPeriodicityF (n + 1)
        let π' : T.X n ⟶ S.X n := M.connesPeriodicityF n
        apply (cancel_epi e.inv).1
        have h : (e.inv ≫ ι) ≫ π ≫ a.hom ≫ T.d (k + 1) k =
            (e.inv ≫ ι) ≫ T.d (n + 1) n ≫ π' ≫ b.hom :=
          M.connesSummandι_periodicityF_comm p r (r + p) n k rfl hpq hk
        change e.inv ≫ (ι ≫ π ≫ a.hom ≫ T.d (k + 1) k) =
          e.inv ≫ (ι ≫ T.d (n + 1) n ≫ π' ≫ b.hom)
        simpa only [Category.assoc] using h
      · exact (M.connesBicomplex_isZero_cell p q (by omega)).eq_of_src _ _
    apply (cancel_mono b.hom).1
    calc
      _ = (F ≫ (a.hom ≫ T.d (k + 1) k ≫ b.inv)) ≫ b.hom :=
        congrArg (fun f : S.X (n + 1) ⟶ S.X n => (F ≫ f) ≫ b.hom) hd
      _ = F ≫ a.hom ≫ T.d (k + 1) k := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = (T.d (n + 1) n ≫ F') ≫ b.hom := by
        simpa only [Category.assoc] using hComp
  · exact (T.isZero_extend_X E n (by
      intro r hr
      change r + 2 = n at hr
      omega)).eq_of_tgt _ _

/-- Periodicity is the chain map discarding the zeroth column. -/
def connesPeriodicity :
    M.connesBicomplex.total c ⟶
      (M.connesBicomplex.total c).extend (ComplexShape.embeddingDown'Add (1 : ℕ) 2) :=
  ChainComplex.ofHom M.connesPeriodicityF M.connesPeriodicityF_comm

/-- Its components are the original total-coordinate projection. -/
theorem connesPeriodicity_f (n : ℕ) : (M.connesPeriodicity).f n = M.connesPeriodicityF n := rfl

/-- The degreewise section puts each original summand one place higher in both
bicomplex indices. It is used only as a degreewise map, without a chain-map claim. -/
def connesPeriodicitySectionF (j : ℕ) :
    ((M.connesBicomplex.total c).extend
      (ComplexShape.embeddingDown'Add (1 : ℕ) 2)).X j ⟶
        (M.connesBicomplex.total c).X j :=
  if hj : 2 ≤ j then
    ((M.connesBicomplex.total c).extendXIso
      (ComplexShape.embeddingDown'Add (1 : ℕ) 2) (Nat.sub_add_cancel hj)).hom ≫
        M.connesBicomplex.totalDesc (fun p q hpq =>
          if hs : p ≤ q then
            (ChainComplex.mixedColumnIso M.underlying p (q - p) q
              (Nat.sub_add_cancel hs)).hom ≫
                M.connesSummandι (p + 1) (q - p) (q + 1) j (by omega)
                  (by change p + q = j - 2 at hpq; omega)
          else 0)
  else 0

/-- The section preserves the mixed-degree coordinate and raises both cell indices. -/
@[reassoc]
theorem connesSummandι_periodicitySectionF (p r q k j : ℕ)
    (hr : r + p = q) (hq : p + q = k) (hj : k + 2 = j) :
    M.connesSummandι p r q k hr hq ≫
        ((M.connesBicomplex.total c).extendXIso
          (ComplexShape.embeddingDown'Add (1 : ℕ) 2) hj).inv ≫
            M.connesPeriodicitySectionF j =
      M.connesSummandι (p + 1) r (q + 1) j (by omega) (by omega) := by
  have hn : 2 ≤ j := by omega
  have hs : p ≤ q := by omega
  obtain rfl : k = j - 2 := by omega
  obtain rfl : r = q - p := by omega
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let S : ChainComplex C ℕ := T.extend E
  let e : (B.X p).X q ≅ M.underlying.X (q - p) :=
    ChainComplex.mixedColumnIso M.underlying p (q - p) q hr
  let a : S.X j ≅ T.X (j - 2) := T.extendXIso E hj
  let ι : (B.X p).X q ⟶ T.X (j - 2) := B.ιTotal c p q (j - 2) hq
  let κ : M.underlying.X (q - p) ⟶ T.X j :=
    M.connesSummandι (p + 1) (q - p) (q + 1) j (by omega) (by omega)
  let σ : S.X j ⟶ T.X j := M.connesPeriodicitySectionF j
  let τ : T.X (j - 2) ⟶ T.X j := B.totalDesc (fun p q hpq =>
    if hs : p ≤ q then
      (ChainComplex.mixedColumnIso M.underlying p (q - p) q
        (Nat.sub_add_cancel hs)).hom ≫
          M.connesSummandι (p + 1) (q - p) (q + 1) j (by omega)
            (by change p + q = j - 2 at hpq; omega)
    else 0)
  have hσ : σ = a.hom ≫ τ := dite_eq_left hn
  have hι : ι ≫ τ = e.hom ≫ κ := by
    change B.ιTotal c p q (j - 2) hq ≫ B.totalDesc (A := T.X j) _ = _
    refine (B.ι_totalDesc (f := _) p q hq).trans ?_
    exact dite_eq_left hs
  change (e.inv ≫ ι) ≫ a.inv ≫ σ = κ
  calc
    _ = (e.inv ≫ ι) ≫ a.inv ≫ (a.hom ≫ τ) :=
      congrArg (fun f : S.X j ⟶ T.X j => (e.inv ≫ ι) ≫ a.inv ≫ f) hσ
    _ = e.inv ≫ (ι ≫ τ) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = e.inv ≫ (e.hom ≫ κ) :=
      congrArg (fun f : (B.X p).X q ⟶ T.X j => e.inv ≫ f) hι
    _ = κ := by simp only [Iso.inv_hom_id_assoc]

/-- On every surviving summand, projection followed by the degreewise section is identity. -/
@[reassoc]
theorem connesSummandι_periodicityF_sectionF (p r q j : ℕ)
    (hr : r + (p + 1) = q) (hj : (p + 1) + q = j) :
    M.connesSummandι (p + 1) r q j hr hj ≫ M.connesPeriodicityF j ≫
        M.connesPeriodicitySectionF j = M.connesSummandι (p + 1) r q j hr hj := by
  let k := j - 2
  have hk : k + 2 = j := by omega
  let e := (M.connesBicomplex.total c).extendXIso
    (ComplexShape.embeddingDown'Add (1 : ℕ) 2) hk
  have hq : q - 1 + 1 = q := by omega
  calc
    _ = (M.connesSummandι (p + 1) r q j hr hj ≫ M.connesPeriodicityF j ≫ e.hom) ≫
        (e.inv ≫ M.connesPeriodicitySectionF j) := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = M.connesSummandι p r (q - 1) k (by omega) (by omega) ≫
        e.inv ≫ M.connesPeriodicitySectionF j := by
      rw [M.connesSummandι_periodicityF]
    _ = _ := by
      simpa only [hq] using
        M.connesSummandι_periodicitySectionF p r (q - 1) k j (by omega) (by omega) hk

/-- The original periodicity projection has its actual degreewise right inverse. -/
theorem connesPeriodicitySectionF_comp_periodicityF (j : ℕ) :
    M.connesPeriodicitySectionF j ≫ M.connesPeriodicityF j = 𝟙 _ := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 2
  by_cases hj : 2 ≤ j
  · let k := j - 2
    have hk : k + 2 = j := Nat.sub_add_cancel hj
    let S : ChainComplex C ℕ := T.extend E
    let e : S.X j ≅ T.X k := T.extendXIso E hk
    let F : T.X j ⟶ S.X j := M.connesPeriodicityF j
    let G : S.X j ⟶ T.X j := M.connesPeriodicitySectionF j
    change G ≫ F = 𝟙 (S.X j)
    have hComp : e.inv ≫ G ≫ F ≫ e.hom = 𝟙 (T.X k) := by
      apply HomologicalComplex₂.total.hom_ext
      intro p q hpq
      by_cases hs : p ≤ q
      · obtain ⟨r, rfl⟩ : ∃ r, q = r + p := ⟨q - p, (Nat.sub_add_cancel hs).symm⟩
        let a : (B.X p).X (r + p) ≅ M.underlying.X r :=
          ChainComplex.mixedColumnIso M.underlying p r (r + p) rfl
        let ι : (B.X p).X (r + p) ⟶ T.X k := B.ιTotal c p (r + p) k hpq
        let σ : S.X j ⟶ T.X j := M.connesPeriodicitySectionF j
        let π : T.X j ⟶ S.X j := M.connesPeriodicityF j
        apply (cancel_epi a.inv).1
        have hsum : p + (r + p) = k := hpq
        let i : M.underlying.X r ⟶ T.X k :=
          M.connesSummandι p r (r + p) k rfl hpq
        let i' : M.underlying.X r ⟶ T.X j :=
          M.connesSummandι (p + 1) r (r + p + 1) j (by omega) (by omega)
        have hG : i ≫ e.inv ≫ G = i' :=
          M.connesSummandι_periodicitySectionF p r (r + p) k j rfl hpq hk
        have hF : i' ≫ F ≫ e.hom = i := by
          have h : i' ≫ F ≫ e.hom =
              M.connesSummandι p r (r + p + 1 - 1) k (by omega) (by omega) :=
            M.connesSummandι_periodicityF p r (r + p + 1) j k (by omega) (by omega) hk
          simpa only [Nat.add_sub_cancel] using h
        have h' : (a.inv ≫ ι) ≫ e.inv ≫ σ ≫ π ≫ e.hom = a.inv ≫ ι := by
          change i ≫ e.inv ≫ G ≫ F ≫ e.hom = i
          calc
            _ = (i ≫ e.inv ≫ G) ≫ F ≫ e.hom := by
              simp only [Category.assoc]
            _ = i' ≫ F ≫ e.hom :=
              congrArg (fun f : M.underlying.X r ⟶ T.X j => f ≫ F ≫ e.hom) hG
            _ = i := hF
        change a.inv ≫ (ι ≫ e.inv ≫ σ ≫ π ≫ e.hom) = a.inv ≫ (ι ≫ 𝟙 (T.X k))
        simpa only [Category.assoc, Category.comp_id] using h'
      · exact (M.connesBicomplex_isZero_cell p q (by omega)).eq_of_src _ _
    apply (cancel_mono e.hom).1
    apply (cancel_epi e.inv).1
    calc
      _ = e.inv ≫ G ≫ F ≫ e.hom :=
        congrArg (fun f : S.X j ⟶ T.X k => e.inv ≫ f) (Category.assoc G F e.hom)
      _ = 𝟙 (T.X k) := hComp
      _ = e.inv ≫ (𝟙 (S.X j) ≫ e.hom) :=
        ((congrArg (fun f : S.X j ⟶ T.X k => e.inv ≫ f)
          (Category.id_comp e.hom)).trans e.inv_hom_id).symm
  · exact (T.isZero_extend_X E j (by
      intro r hr
      change r + 2 = j at hr
      omega)).eq_of_src _ _

variable [HasFiniteCoproducts C]

/-- The zeroth-column inclusion is killed by the constructed chain projection. -/
@[reassoc]
theorem partialTotalι_connesPeriodicity :
    M.connesBicomplex.partialTotalι 0 ≫ M.connesPeriodicity = 0 := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := B.total c
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let S : ChainComplex C ℕ := T.extend E
  let P : ChainComplex C ℕ := B.partialTotal 0
  let ι : P ⟶ T := B.partialTotalι 0
  let π : T ⟶ S := M.connesPeriodicity
  change ι ≫ π = 0
  apply B.partialTotal_hom_ext 0
  intro i q j hij
  have hi : i = (0 : Fin 1) := by
    apply Fin.ext
    have h := i.isLt
    omega
  subst i
  let a : (B.X 0).X q ≅ M.underlying.X q :=
    ChainComplex.mixedColumnIso M.underlying 0 q q rfl
  let i₀ : (B.X 0).X q ⟶ P.X j := B.partialTotalComponent 0 (0 : Fin 1) q j hij
  let iT : (B.X 0).X q ⟶ T.X j := B.ιTotal c 0 q j hij
  let πj : T.X j ⟶ S.X j := M.connesPeriodicityF j
  have hi : i₀ ≫ ι.f j = iT := B.partialTotalComponent_comp_partialTotalι 0 0 q j hij
  have hz : iT ≫ πj = 0 := by
    apply (cancel_epi a.inv).1
    have h : (a.inv ≫ iT) ≫ πj = 0 :=
      M.connesSummandι_periodicityF_zero q q j rfl hij
    change a.inv ≫ (iT ≫ πj) = a.inv ≫ 0
    simpa only [Category.assoc, comp_zero] using h
  change i₀ ≫ (ι.f j ≫ πj) = i₀ ≫ 0
  exact ((Category.assoc i₀ (ι.f j) πj).symm.trans
    ((congrArg (fun f : (B.X 0).X q ⟶ T.X j => f ≫ πj) hi).trans hz)).trans
      ((comp_zero : i₀ ≫ (0 : P.X j ⟶ S.X j) = 0).symm)

end MixedComplex

namespace MixedComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (M : MixedComplex C)

local notation "c" => ComplexShape.down ℕ

/-- Projection and section agree with identity after the column-zero quotient. -/
@[reassoc]
theorem connesPeriodicityF_sectionF_cokernelπ (j : ℕ) :
    M.connesPeriodicityF j ≫ M.connesPeriodicitySectionF j ≫
        (cokernel.π (M.connesBicomplex.partialTotalι 0)).f j =
      (cokernel.π (M.connesBicomplex.partialTotalι 0)).f j := by
  let B := M.connesBicomplex
  let π := cokernel.π (B.partialTotalι 0)
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  by_cases hs : p ≤ q
  · obtain ⟨r, rfl⟩ : ∃ r, q = r + p := ⟨q - p, (Nat.sub_add_cancel hs).symm⟩
    let T : ChainComplex C ℕ := B.total c
    let Q : ChainComplex C ℕ := cokernel (B.partialTotalι 0)
    let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
    let U : ChainComplex C ℕ := T.extend E
    let F : T.X j ⟶ U.X j := M.connesPeriodicityF j
    let G : U.X j ⟶ T.X j := M.connesPeriodicitySectionF j
    let πj : T.X j ⟶ Q.X j := π.f j
    let e : (B.X p).X (r + p) ≅ M.underlying.X r :=
      ChainComplex.mixedColumnIso M.underlying p r (r + p) rfl
    let i : (B.X p).X (r + p) ⟶ T.X j := B.ιTotal c p (r + p) j hpq
    let a : M.underlying.X r ⟶ T.X j := M.connesSummandι p r (r + p) j rfl hpq
    have ha : a = e.inv ≫ i := rfl
    apply (cancel_epi e.inv).1
    change e.inv ≫ (i ≫ F ≫ G ≫ πj) = e.inv ≫ (i ≫ πj)
    have h : a ≫ F ≫ G ≫ πj = a ≫ πj := by
      cases p with
      | zero =>
          have hNative : i ≫ πj = 0 :=
            B.ιTotal_cokernel_partialTotalι_π_eq_zero 0 0 (r + 0) j (by decide) hpq
          have hπ : a ≫ πj = 0 := by
            calc
              _ = (e.inv ≫ i) ≫ πj :=
                congrArg (fun f : M.underlying.X r ⟶ T.X j => f ≫ πj) ha
              _ = e.inv ≫ (i ≫ πj) := Category.assoc _ _ _
              _ = 0 :=
                (congrArg (fun f : (B.X 0).X (r + 0) ⟶ Q.X j => e.inv ≫ f)
                  hNative).trans comp_zero
          have hF : a ≫ F = 0 := M.connesSummandι_periodicityF_zero r (r + 0) j rfl hpq
          calc
            _ = (a ≫ F) ≫ G ≫ πj := by simp only [Category.assoc]
            _ = 0 := by rw [hF]; simp only [zero_comp]
            _ = a ≫ πj := hπ.symm
      | succ p =>
          exact M.connesSummandι_periodicityF_sectionF_assoc p r (r + (p + 1)) j
            rfl hpq πj
    simpa only [ha, Category.assoc] using h
  · exact (M.connesBicomplex_isZero_cell p q (by omega)).eq_of_src _ _

/-- The mixed tail map descends the original periodicity through the cokernel. -/
def connesTailNatMap :
    cokernel (M.connesBicomplex.partialTotalι 0) ⟶
      M.connesTotal.extend (ComplexShape.embeddingDown'Add (1 : ℕ) 2) :=
  cokernel.desc (M.connesBicomplex.partialTotalι 0) M.connesPeriodicity
    M.partialTotalι_connesPeriodicity

/-- The descended map retains exactly the original total projection. -/
@[reassoc]
theorem cokernelπ_connesTailNatMap :
    cokernel.π (M.connesBicomplex.partialTotalι 0) ≫ M.connesTailNatMap =
      M.connesPeriodicity :=
  cokernel.π_desc _ _ _

/-- The characteristic equation holds on every original degree. -/
@[reassoc]
theorem cokernelπ_connesTailNatMap_f (j : ℕ) :
    (cokernel.π (M.connesBicomplex.partialTotalι 0)).f j ≫
        (M.connesTailNatMap).f j = M.connesPeriodicityF j := by
  simpa only [HomologicalComplex.comp_f, connesPeriodicity_f] using
    HomologicalComplex.congr_hom M.cokernelπ_connesTailNatMap j

/-- Its inverse is degreewise from the original section and quotient projection. -/
instance connesTailNatMap_isIso : IsIso M.connesTailNatMap := by
  let T : ChainComplex C ℕ := M.connesTotal
  let Q : ChainComplex C ℕ := cokernel (M.connesBicomplex.partialTotalι 0)
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let U : ChainComplex C ℕ := T.extend E
  let g : Q ⟶ U := M.connesTailNatMap
  let π : T ⟶ Q := cokernel.π (M.connesBicomplex.partialTotalι 0)
  letI : ∀ j : ℕ, IsIso (g.f j) := fun j => by
    let F : T.X j ⟶ U.X j := M.connesPeriodicityF j
    let S : U.X j ⟶ T.X j := M.connesPeriodicitySectionF j
    let πj : T.X j ⟶ Q.X j := π.f j
    let v : U.X j ⟶ Q.X j := S ≫ πj
    letI : Epi πj := by
      change Epi ((HomologicalComplex.eval C c j).map π)
      infer_instance
    have hπg : πj ≫ g.f j = F := M.cokernelπ_connesTailNatMap_f j
    have hFSπ : F ≫ S ≫ πj = πj := M.connesPeriodicityF_sectionF_cokernelπ j
    have hSF : S ≫ F = 𝟙 (U.X j) := M.connesPeriodicitySectionF_comp_periodicityF j
    have hgv : g.f j ≫ v = 𝟙 (Q.X j) := by
      apply (cancel_epi πj).1
      calc
        πj ≫ (g.f j ≫ v) = (πj ≫ g.f j) ≫ S ≫ πj := by
          simp only [v, Category.assoc]
        _ = F ≫ S ≫ πj :=
          congrArg (fun f : T.X j ⟶ U.X j => f ≫ S ≫ πj) hπg
        _ = πj := hFSπ
        _ = πj ≫ 𝟙 (Q.X j) := (Category.comp_id _).symm
    have hvg : v ≫ g.f j = 𝟙 (U.X j) := by
      calc
        _ = (S ≫ πj) ≫ g.f j := rfl
        _ = S ≫ (πj ≫ g.f j) := Category.assoc _ _ _
        _ = S ≫ F := congrArg (fun f : T.X j ⟶ U.X j => S ≫ f) hπg
        _ = 𝟙 (U.X j) := hSF
    exact (show Q.X j ≅ U.X j from
      { hom := g.f j
        inv := v
        hom_inv_id := hgv
        inv_hom_id := hvg }).isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components g

/-- The column-zero cokernel is the Connes total translated by two. -/
def connesTailNatIso :
    cokernel (M.connesBicomplex.partialTotalι 0) ≅
      M.connesTotal.extend (ComplexShape.embeddingDown'Add (1 : ℕ) 2) :=
  asIso M.connesTailNatMap

/-- The tail isomorphism keeps each surviving original mixed summand. -/
@[reassoc]
theorem connesSummandι_cokernelπ_tailNatIso (p r q j k : ℕ)
    (hr : r + (p + 1) = q) (hj : (p + 1) + q = j) (hk : k + 2 = j) :
    M.connesSummandι (p + 1) r q j hr hj ≫
        (cokernel.π (M.connesBicomplex.partialTotalι 0)).f j ≫
          M.connesTailNatIso.hom.f j ≫
            (M.connesTotal.extendXIso
              (ComplexShape.embeddingDown'Add (1 : ℕ) 2) hk).hom =
      M.connesSummandι p r (q - 1) k (by omega) (by omega) := by
  let T : ChainComplex C ℕ := M.connesTotal
  let Q : ChainComplex C ℕ := cokernel (M.connesBicomplex.partialTotalι 0)
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let U : ChainComplex C ℕ := T.extend E
  let s : M.underlying.X r ⟶ T.X j := M.connesSummandι (p + 1) r q j hr hj
  let πj : T.X j ⟶ Q.X j := (cokernel.π (M.connesBicomplex.partialTotalι 0)).f j
  let f : Q.X j ⟶ U.X j := M.connesTailNatIso.hom.f j
  let F : T.X j ⟶ U.X j := M.connesPeriodicityF j
  let e : U.X j ≅ T.X k := T.extendXIso E hk
  have hMap : πj ≫ f = F := M.cokernelπ_connesTailNatMap_f j
  have hF : s ≫ F ≫ e.hom = M.connesSummandι p r (q - 1) k (by omega) (by omega) :=
    M.connesSummandι_periodicityF p r q j k hr hj hk
  change s ≫ πj ≫ f ≫ e.hom = _
  calc
    _ = s ≫ (πj ≫ f) ≫ e.hom := by simp only [Category.assoc]
    _ = s ≫ F ≫ e.hom := congrArg (fun a : T.X j ⟶ U.X j => s ≫ a ≫ e.hom) hMap
    _ = _ := hF

/-- In literal bicomplex coordinates the computed natural-degree tail drops both indices by one. -/
@[reassoc]
theorem connesTailNatIso_cell (p q : ℕ) (hpq : p ≤ q) :
    M.connesBicomplex.ιTotal c (p + 1) (q + 1) (p + q + 2) (by
      change (p + 1) + (q + 1) = p + q + 2
      omega) ≫
        (cokernel.π (M.connesBicomplex.partialTotalι 0)).f (p + q + 2) ≫
          M.connesTailNatIso.hom.f (p + q + 2) ≫
            (M.connesTotal.extendXIso
              (ComplexShape.embeddingDown'Add (1 : ℕ) 2)
              (show p + q + 2 = p + q + 2 from rfl)).hom =
      (ChainComplex.mixedColumnIso M.underlying (p + 1) (q - p) (q + 1) (by omega)).hom ≫
        (ChainComplex.mixedColumnIso M.underlying p (q - p) q
          (Nat.sub_add_cancel hpq)).inv ≫ M.connesBicomplex.ιTotal c p q (p + q) rfl := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := M.connesTotal
  let Q : ChainComplex C ℕ := cokernel (B.partialTotalι 0)
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let U : ChainComplex C ℕ := T.extend E
  let s : (B.X (p + 1)).X (q + 1) ≅ M.underlying.X (q - p) :=
    ChainComplex.mixedColumnIso M.underlying (p + 1) (q - p) (q + 1) (by omega)
  let t : (B.X p).X q ≅ M.underlying.X (q - p) :=
    ChainComplex.mixedColumnIso M.underlying p (q - p) q (Nat.sub_add_cancel hpq)
  let iS : (B.X (p + 1)).X (q + 1) ⟶ T.X (p + q + 2) :=
    B.ιTotal c (p + 1) (q + 1) (p + q + 2) (by
      change (p + 1) + (q + 1) = p + q + 2
      omega)
  let iT : (B.X p).X q ⟶ T.X (p + q) := B.ιTotal c p q (p + q) rfl
  let πj : T.X (p + q + 2) ⟶ Q.X (p + q + 2) :=
    (cokernel.π (B.partialTotalι 0)).f (p + q + 2)
  let f : Q.X (p + q + 2) ⟶ U.X (p + q + 2) := M.connesTailNatIso.hom.f (p + q + 2)
  let e : U.X (p + q + 2) ≅ T.X (p + q) := T.extendXIso E rfl
  have hS : M.connesSummandι (p + 1) (q - p) (q + 1) (p + q + 2)
      (by omega) (by omega) = s.inv ≫ iS := rfl
  have hT : M.connesSummandι p (q - p) (q + 1 - 1) (p + q) (by omega) (by omega) =
      t.inv ≫ iT := by
    change t.inv ≫ iT = t.inv ≫ iT
    rfl
  have h : (s.inv ≫ iS) ≫ πj ≫ f ≫ e.hom = t.inv ≫ iT := by
    calc
      _ = M.connesSummandι (p + 1) (q - p) (q + 1) (p + q + 2) (by omega) (by omega) ≫
          πj ≫ f ≫ e.hom :=
        congrArg (fun a : M.underlying.X (q - p) ⟶ T.X (p + q + 2) =>
          a ≫ πj ≫ f ≫ e.hom) hS.symm
      _ = M.connesSummandι p (q - p) (q + 1 - 1) (p + q) (by omega) (by omega) :=
        M.connesSummandι_cokernelπ_tailNatIso p (q - p) (q + 1) (p + q + 2) (p + q)
          (by omega) (by omega) rfl
      _ = t.inv ≫ iT := hT
  change iS ≫ πj ≫ f ≫ e.hom = s.hom ≫ t.inv ≫ iT
  apply (cancel_epi s.inv).1
  calc
    _ = (s.inv ≫ iS) ≫ πj ≫ f ≫ e.hom := by simp only [Category.assoc]
    _ = t.inv ≫ iT := h
    _ = s.inv ≫ (s.hom ≫ t.inv ≫ iT) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The tail isomorphism expressed in integer chain degrees. -/
def connesTailIso :
    (cokernel (M.connesBicomplex.partialTotalι 0)).extend
        (ComplexShape.embeddingDownNatToIntShift 0) ≅
      M.connesTotal.extend (ComplexShape.embeddingDownNatToIntShift 2) :=
  ((ComplexShape.embeddingDownNatToIntShift 0).extendFunctor C).mapIso M.connesTailNatIso ≪≫
    HomologicalComplex.extendNatAddIntIso M.connesTotal 2

/-- The integer tail comparison retains the exact original mixed-cell map. -/
@[reassoc]
theorem connesTailIso_cell (p q : ℕ) (hpq : p ≤ q) :
    M.connesBicomplex.partialTotalCokernelGenerator 0 0 (p + 1) (q + 1)
        (p + q + 2) (by omega) (2 + ((p + q : ℕ) : ℤ)) (by
          rw [ComplexShape.embeddingDownNatToIntShift_f]
          push_cast
          omega) ≫
      M.connesTailIso.hom.f (2 + ((p + q : ℕ) : ℤ)) ≫
        (HomologicalComplex.extendDownNatToIntShiftXIso M.connesTotal 2 (p + q)).hom =
      (ChainComplex.mixedColumnIso M.underlying (p + 1) (q - p) (q + 1) (by omega)).hom ≫
        (ChainComplex.mixedColumnIso M.underlying p (q - p) q
          (Nat.sub_add_cancel hpq)).inv ≫ M.connesBicomplex.ιTotal c p q (p + q) rfl := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := M.connesTotal
  let Q : ChainComplex C ℕ := cokernel (B.partialTotalι 0)
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := ComplexShape.embeddingDown'Add (1 : ℕ) 2
  let e₀ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 0
  let e₂ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 2
  let z : ℤ := 2 + ((p + q : ℕ) : ℤ)
  have hz : e₀.f (p + q + 2) = z := by
    change (0 : ℤ) + ((p + q + 2 : ℕ) : ℤ) = 2 + ((p + q : ℕ) : ℤ)
    push_cast
    omega
  let N : Q ≅ T.extend E := M.connesTailNatIso
  let a : (Q.extend e₀).X z ≅ Q.X (p + q + 2) := Q.extendXIso e₀ hz
  let b : ((T.extend E).extend e₀).X z ≅ (T.extend E).X (p + q + 2) :=
    (T.extend E).extendXIso e₀ hz
  let d : (T.extend E).X (p + q + 2) ≅ T.X (p + q) := T.extendXIso E rfl
  let e : (T.extend e₂).X z ≅ T.X (p + q) :=
    HomologicalComplex.extendDownNatToIntShiftXIso T 2 (p + q)
  let u : Q.extend e₀ ⟶ (T.extend E).extend e₀ := HomologicalComplex.extendMap N.hom e₀
  let v : (T.extend E).extend e₀ ≅ T.extend e₂ := HomologicalComplex.extendNatAddIntIso T 2
  let o : ((T.extend E).extend e₀).X z ≅ T.X (p + q) :=
    HomologicalComplex.extendNatAddIntRestrictionXIso T 2 (p + q)
  let πj : T.X (p + q + 2) ⟶ Q.X (p + q + 2) :=
    (cokernel.π (B.partialTotalι 0)).f (p + q + 2)
  let i : (B.X (p + 1)).X (q + 1) ⟶ T.X (p + q + 2) :=
    B.ιTotal c (p + 1) (q + 1) (p + q + 2) (by
      change (p + 1) + (q + 1) = p + q + 2
      omega)
  let g : (B.X (p + 1)).X (q + 1) ⟶ (Q.extend e₀).X z :=
    B.partialTotalCokernelGenerator 0 0 (p + 1) (q + 1) (p + q + 2) (by omega) z hz
  let F : (Q.extend e₀).X z ⟶ (T.extend e₂).X z := M.connesTailIso.hom.f z
  have hG : g = i ≫ πj ≫ a.inv := rfl
  have hF : F = u.f z ≫ v.hom.f z := rfl
  have hu : u.f z = a.hom ≫ N.hom.f (p + q + 2) ≫ b.inv :=
    HomologicalComplex.extendMap_f N.hom e₀ hz
  have ho : o.hom = b.hom ≫ d.hom := rfl
  have hV : v.hom.f z = o.hom ≫ e.inv :=
    HomologicalComplex.extendNatAddIntIso_hom_f T 2 (p + q)
  have hv : b.inv ≫ v.hom.f z ≫ e.hom = d.hom := by
    calc
      _ = b.inv ≫ (o.hom ≫ e.inv) ≫ e.hom :=
        congrArg (fun f : ((T.extend E).extend e₀).X z ⟶ (T.extend e₂).X z =>
          b.inv ≫ f ≫ e.hom) hV
      _ = b.inv ≫ ((b.hom ≫ d.hom) ≫ e.inv) ≫ e.hom :=
        congrArg (fun f : ((T.extend E).extend e₀).X z ⟶ T.X (p + q) =>
          b.inv ≫ (f ≫ e.inv) ≫ e.hom) ho
      _ = d.hom ≫ (e.inv ≫ e.hom) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = d.hom := by rw [e.inv_hom_id, Category.comp_id]
  change g ≫ F ≫ e.hom = _
  rw [hG, hF, hu]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hv]
  exact M.connesTailNatIso_cell p q hpq

/-- The constructed integer tail has the precise component specification of generic mixed SBI. -/
theorem connesTailIso_hom_spec (p q : ℕ) (hpq : p ≤ q) :
    genericMixedTailSourceComponent M.connesDoubleData p q ≫
        M.connesTailIso.hom.f (2 + ((p + q : ℕ) : ℤ)) =
      genericMixedTailTargetComponent M.connesDoubleData p q hpq := by
  let B : HomologicalComplex₂ C c c := M.connesBicomplex
  let T : ChainComplex C ℕ := M.connesTotal
  let Q : ChainComplex C ℕ := cokernel (B.partialTotalι 0)
  let e₀ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 0
  let e₂ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) := ComplexShape.embeddingDownNatToIntShift 2
  let z : ℤ := 2 + ((p + q : ℕ) : ℤ)
  let e : (T.extend e₂).X z ≅ T.X (p + q) :=
    HomologicalComplex.extendDownNatToIntShiftXIso T 2 (p + q)
  let cell (r : ℕ) (hr : r + (p + 1) = q + 1) :
      (B.X (p + 1)).X (q + 1) ≅ M.underlying.X r :=
    ChainComplex.mixedColumnIso M.underlying (p + 1) r (q + 1) hr
  have hTransport (r₁ r₂ : ℕ) (hr₁ : r₁ + (p + 1) = q + 1)
      (hr₂ : r₂ + (p + 1) = q + 1) (h : r₁ = r₂) :
      (cell r₁ hr₁).hom ≫ eqToHom (congrArg (fun r => M.underlying.X r) h) =
        (cell r₂ hr₂).hom := by
    subst r₂
    change (cell r₁ hr₁).hom ≫ 𝟙 (M.underlying.X r₁) = (cell r₁ hr₁).hom
    exact Category.comp_id _
  let a : (B.X (p + 1)).X (q + 1) ≅ M.underlying.X (q - p) := cell (q - p) (by omega)
  let b : (B.X p).X q ≅ M.underlying.X (q - p) :=
    ChainComplex.mixedColumnIso M.underlying p (q - p) q (Nat.sub_add_cancel hpq)
  let c₀ : (B.X (p + 1)).X (q + 1) ≅ M.underlying.X (q + 1 - (p + 1)) :=
    M.connesDoubleData.objIso (p + 1) (q + 1) (by omega)
  let τ : M.underlying.X (q + 1 - (p + 1)) ⟶ M.underlying.X (q - p) :=
    eqToHom (congrArg (fun r => M.underlying.X r) (Nat.add_sub_add_right q 1 p))
  let i : (B.X p).X q ⟶ T.X (p + q) := B.ιTotal c p q (p + q) rfl
  let g : (B.X (p + 1)).X (q + 1) ⟶ (Q.extend e₀).X z :=
    genericMixedTailSourceComponent M.connesDoubleData p q
  let F : (Q.extend e₀).X z ⟶ (T.extend e₂).X z := M.connesTailIso.hom.f z
  have he : c₀.hom ≫ τ = a.hom := by
    change (cell (q + 1 - (p + 1)) (by omega)).hom ≫
      eqToHom (congrArg (fun r => M.underlying.X r) (Nat.add_sub_add_right q 1 p)) =
        (cell (q - p) (by omega)).hom
    exact hTransport (q + 1 - (p + 1)) (q - p) (by omega) (by omega)
      (Nat.add_sub_add_right q 1 p)
  have hTarget : genericMixedTailTargetComponent M.connesDoubleData p q hpq =
      a.hom ≫ b.inv ≫ i ≫ e.inv := by
    change c₀.hom ≫ τ ≫ b.inv ≫ i ≫ e.inv = a.hom ≫ b.inv ≫ i ≫ e.inv
    calc
      _ = (c₀.hom ≫ τ) ≫ (b.inv ≫ i ≫ e.inv) := (Category.assoc _ _ _).symm
      _ = a.hom ≫ (b.inv ≫ i ≫ e.inv) :=
        congrArg (fun f : (B.X (p + 1)).X (q + 1) ⟶ M.underlying.X (q - p) =>
          f ≫ (b.inv ≫ i ≫ e.inv)) he
  have hCell : g ≫ F ≫ e.hom = a.hom ≫ b.inv ≫ i := M.connesTailIso_cell p q hpq
  have hEnd : (a.hom ≫ b.inv ≫ i ≫ e.inv) ≫ e.hom = a.hom ≫ b.inv ≫ i := by
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  have hTargetEval :
      genericMixedTailTargetComponent M.connesDoubleData p q hpq ≫ e.hom =
        a.hom ≫ b.inv ≫ i :=
    (congrArg (fun f : (B.X (p + 1)).X (q + 1) ⟶ (T.extend e₂).X z => f ≫ e.hom)
      hTarget).trans hEnd
  apply (cancel_mono e.hom).1
  change (g ≫ F) ≫ e.hom = genericMixedTailTargetComponent M.connesDoubleData p q hpq ≫ e.hom
  exact ((Category.assoc g F e.hom).trans hCell).trans hTargetEval.symm

/-- Generic mixed cyclic data are constructed from the original mixed complex itself.
Both chain comparisons and their specifications are earned, rather than assumed. -/
def connesCyclicData : GenericMixedCyclicData M where
  model := M.connesDoubleData
  columnMap := M.connesFirstColumnMap
  columnMap_spec q := M.connesFirstColumnMap_spec q
  columnMapQuasiIso := by
    let K : ChainComplex C ℕ := M.underlying
    let P : ChainComplex C ℕ := M.connesBicomplex.partialTotal 0
    let f : K ⟶ P := M.connesFirstColumnMap
    letI : IsIso f := M.connesFirstColumnMap_isIso
    have hf : QuasiIso f := inferInstance
    exact hf
  tailMap := M.connesTailIso.hom
  tailMapIsIso := by
    let Q : ChainComplex C ℕ := cokernel (M.connesBicomplex.partialTotalι 0)
    let T : ChainComplex C ℕ := M.connesTotal
    let a : Q.extend (ComplexShape.embeddingDownNatToIntShift 0) ≅
        T.extend (ComplexShape.embeddingDownNatToIntShift 2) := M.connesTailIso
    exact a.isIso_hom
  tailMap_spec p q h := M.connesTailIso_hom_spec p q h

/-- The mixed SBI presentation has the original b-complex and original total/cokernel. -/
def connesSBIPresentation : ConnesSBIPresentation (A := C) :=
  M.connesCyclicData.toConnesSBIPresentation

/-- The column-zero cokernel already vanishes in its first two chain degrees. -/
theorem isZero_connesTail_X (n : ℕ) (hn : n < 2) :
    IsZero ((cokernel (M.connesBicomplex.partialTotalι 0)).X n) := by
  have h := M.connesTotal.isZero_extend_X
    (ComplexShape.embeddingDown'Add (1 : ℕ) 2) n (by
      intro r hr
      change r + 2 = n at hr
      omega)
  exact h.of_iso ((HomologicalComplex.eval C c n).mapIso M.connesTailNatIso)

end MixedComplex

namespace MixedComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂

universe uB vB

variable {C : Type uB} [Category.{vB} C] [Abelian C] (M : MixedComplex C)

/-- The original b-complex includes in the total through the first column. -/
def connesOrdinaryInclusion : M.underlying ⟶ M.connesTotal :=
  M.connesFirstColumnMap ≫ M.connesBicomplex.partialTotalι 0

/-- Its original degree component is the column-zero total summand. -/
theorem connesOrdinaryInclusion_f (n : ℕ) :
    M.connesOrdinaryInclusion.f n =
      M.connesSummandι 0 n n n rfl (Nat.zero_add n) := by
  let B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) := M.connesBicomplex
  let P : ChainComplex C ℕ := B.partialTotal 0
  let T : ChainComplex C ℕ := M.connesTotal
  let a : (B.X 0).X n ≅ M.underlying.X n :=
    ChainComplex.mixedColumnIso M.underlying 0 n n rfl
  let c : (B.X 0).X n ≅ M.underlying.X n :=
    M.connesDoubleData.objIso 0 n (Nat.zero_le n) ≪≫
      eqToIso (congrArg (mixedObject M) (Nat.sub_zero n))
  let i : (B.X 0).X n ⟶ P.X n :=
    B.partialTotalComponent 0 (0 : Fin 1) n n (Nat.zero_add n)
  let j : (B.X 0).X n ⟶ T.X n := B.ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n)
  let t : P.X n ⟶ T.X n := (B.partialTotalι 0).f n
  have hc : c = a := by
    change a ≪≫ Iso.refl (M.underlying.X n) = a
    exact Iso.trans_refl a
  have hg : (genericMixedColumnιComponent M.connesDoubleData n : M.underlying.X n ⟶ P.X n) =
      c.inv ≫ i := by
    change a.inv ≫ i = (a ≪≫ Iso.refl (M.underlying.X n)).inv ≫ i
    simp only [Iso.trans_inv, Iso.refl_inv, Category.id_comp]
  have hSpec : M.connesFirstColumnMap.f n =
      (genericMixedColumnιComponent M.connesDoubleData n : M.underlying.X n ⟶ P.X n) :=
    M.connesFirstColumnMap_spec n
  have hMap : M.connesFirstColumnMap.f n = a.inv ≫ i :=
    (hSpec.trans hg).trans
      (congrArg (fun e : (B.X 0).X n ≅ M.underlying.X n => e.inv ≫ i) hc)
  have hi : i ≫ t = j := B.partialTotalComponent_comp_partialTotalι 0 (0 : Fin 1) n n (Nat.zero_add n)
  change M.connesFirstColumnMap.f n ≫ t = a.inv ≫ j
  calc
    _ = (a.inv ≫ i) ≫ t := congrArg (fun f : M.underlying.X n ⟶ P.X n => f ≫ t) hMap
    _ = a.inv ≫ (i ≫ t) := Category.assoc _ _ _
    _ = a.inv ≫ j := congrArg (fun f : (B.X 0).X n ⟶ T.X n => a.inv ≫ f) hi

/-- Original cycles lift to the middle complex through the degreewise tail section. -/
def connesBoundaryLiftX₂ (n : ℕ) : M.underlying.cycles n ⟶ M.connesTotal.X (n + 2) :=
  M.underlying.iCycles n ≫ M.connesOrdinaryInclusion.f n ≫
    (M.connesTotal.extendXIso (ComplexShape.embeddingDown'Add (1 : ℕ) 2) rfl).inv ≫
      M.connesPeriodicitySectionF (n + 2)

/-- The section lift is precisely the first positive-column mixed-degree summand. -/
theorem connesBoundaryLiftX₂_eq (n : ℕ) :
    M.connesBoundaryLiftX₂ n = M.underlying.iCycles n ≫
      M.connesSummandι 1 n (n + 1) (n + 2) rfl (by omega) := by
  let T : ChainComplex C ℕ := M.connesTotal
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := partialTotalOuterEmbedding 2
  let U : ChainComplex C ℕ := T.extend E
  let e : U.X (n + 2) ≅ T.X n := T.extendXIso E rfl
  let s : U.X (n + 2) ⟶ T.X (n + 2) := M.connesPeriodicitySectionF (n + 2)
  let i₀ : M.underlying.X n ⟶ T.X n := M.connesSummandι 0 n n n rfl (Nat.zero_add n)
  let i₁ : M.underlying.X n ⟶ T.X (n + 2) := M.connesSummandι 1 n (n + 1) (n + 2) rfl (by omega)
  let z : M.underlying.cycles n ⟶ M.underlying.X n := M.underlying.iCycles n
  have hs : i₀ ≫ e.inv ≫ s = i₁ :=
    M.connesSummandι_periodicitySectionF 0 n n n (n + 2) rfl (Nat.zero_add n) rfl
  have hi : M.connesOrdinaryInclusion.f n = i₀ := M.connesOrdinaryInclusion_f n
  change z ≫ M.connesOrdinaryInclusion.f n ≫ e.inv ≫ s = z ≫ i₁
  calc
    _ = z ≫ i₀ ≫ e.inv ≫ s :=
      congrArg (fun f : M.underlying.X n ⟶ T.X n => z ≫ f ≫ e.inv ≫ s) hi
    _ = z ≫ i₁ := congrArg (fun f : M.underlying.X n ⟶ T.X (n + 2) => z ≫ f) hs

/-- The ordinary B action gives the cycle lift into column zero in degree n+1. -/
def connesBoundaryFirstCycle (n : ℕ) :
    M.underlying.cycles n ⟶ (M.connesBicomplex.partialTotal 0).cycles (n + 1) :=
  M.cyclesB n ≫ cyclesMap M.connesFirstColumnMap (n + 1)

/-- Its chain-component value is the original B applied to the original cycle. -/
@[reassoc]
theorem connesBoundaryFirstCycle_iCycles (n : ℕ) :
    M.connesBoundaryFirstCycle n ≫ (M.connesBicomplex.partialTotal 0).iCycles (n + 1) =
      M.underlying.iCycles n ≫ M.B n ≫ M.connesFirstColumnMap.f (n + 1) := by
  rw [connesBoundaryFirstCycle, Category.assoc, cyclesMap_i]
  rw [← Category.assoc, M.cyclesB_iCycles n, Category.assoc]

/-- The middle lift has differential B in column zero: its b term vanishes on cycles. -/
theorem connesBoundaryLiftX₂_d (n : ℕ) :
    M.connesBoundaryLiftX₂ n ≫ M.connesTotal.d (n + 2) (n + 1) =
      M.connesBoundaryFirstCycle n ≫ (M.connesBicomplex.partialTotal 0).iCycles (n + 1) ≫
        (M.connesBicomplex.partialTotalι 0).f (n + 1) := by
  rw [connesBoundaryLiftX₂_eq, M.connesBoundaryFirstCycle_iCycles_assoc]
  change (M.underlying.iCycles n ≫
      M.connesSummandι 1 n (n + 1) (n + 2) rfl (by omega)) ≫
        M.connesTotal.d (n + 2) (n + 1) =
    M.underlying.iCycles n ≫ M.B n ≫ M.connesOrdinaryInclusion.f (n + 1)
  rw [connesOrdinaryInclusion_f, Category.assoc]
  cases n with
  | zero =>
      rw [M.connesSummandι_d_zero_degree 0 1 2 1 rfl rfl rfl]
  | succ n =>
      rw [M.connesSummandι_d 0 n (n + 2) (n + 3) (n + 2) rfl (by omega) (Nat.zero_add _)]
      simp only [Preadditive.comp_add, Category.assoc,
        HomologicalComplex.iCycles_d_assoc, zero_comp, add_zero]

/-- The image of the middle lift in the original column-zero cokernel. -/
def connesBoundaryLiftX₃ (n : ℕ) :
    M.underlying.cycles n ⟶ (cokernel (M.connesBicomplex.partialTotalι 0)).X (n + 2) :=
  M.connesBoundaryLiftX₂ n ≫ (cokernel.π (M.connesBicomplex.partialTotalι 0)).f (n + 2)

/-- The lift is a cycle in the quotient, by the original cokernel relation. -/
theorem connesBoundaryLiftX₃_d (n : ℕ) :
    M.connesBoundaryLiftX₃ n ≫
        (cokernel (M.connesBicomplex.partialTotalι 0)).d (n + 2) (n + 1) = 0 := by
  let f := M.connesBicomplex.partialTotalι 0
  let π := cokernel.π f
  have hπ : f.f (n + 1) ≫ π.f (n + 1) = 0 := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      HomologicalComplex.congr_hom (cokernel.condition f) (n + 1)
  have hD : M.connesBoundaryLiftX₂ n ≫ M.connesTotal.d (n + 2) (n + 1) =
      M.connesBoundaryFirstCycle n ≫ (M.connesBicomplex.partialTotal 0).iCycles (n + 1) ≫
        f.f (n + 1) := M.connesBoundaryLiftX₂_d n
  change (M.connesBoundaryLiftX₂ n ≫ π.f (n + 2)) ≫
    (cokernel f).d (n + 2) (n + 1) = 0
  rw [Category.assoc, π.comm, ← Category.assoc, hD]
  simp only [Category.assoc]
  rw [hπ, comp_zero, comp_zero]

/-- The quotient lift, placed in the native cycle object. -/
def connesBoundaryTailCycle (n : ℕ) :
    M.underlying.cycles n ⟶ (cokernel (M.connesBicomplex.partialTotalι 0)).cycles (n + 2) :=
  (cokernel (M.connesBicomplex.partialTotalι 0)).liftCycles
    (M.connesBoundaryLiftX₃ n) (n + 1)
      ((ComplexShape.down ℕ).next_eq' (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1)))
        (M.connesBoundaryLiftX₃_d n)

/-- The cycle object retains the original quotient lift. -/
@[reassoc]
theorem connesBoundaryTailCycle_iCycles (n : ℕ) :
    M.connesBoundaryTailCycle n ≫
        (cokernel (M.connesBicomplex.partialTotalι 0)).iCycles (n + 2) = M.connesBoundaryLiftX₃ n := by
  simp only [connesBoundaryTailCycle, HomologicalComplex.liftCycles_i]

/-- The quotient cycle lift returns the original cycle after the two-degree tail comparison. -/
theorem connesBoundaryLiftX₃_coordinates (n : ℕ) :
    M.connesBoundaryLiftX₃ n ≫
        ((cokernel (M.connesBicomplex.partialTotalι 0)).extendXIso
          (ComplexShape.embeddingDownNatToIntShift 0) rfl).inv ≫
            M.connesTailIso.hom.f (0 + ((n + 2 : ℕ) : ℤ)) ≫
              ((M.connesTotal.extend (ComplexShape.embeddingDownNatToIntShift 2)).XIsoOfEq
                (by omega : (0 : ℤ) + ((n + 2 : ℕ) : ℤ) = 2 + (n : ℤ))).hom ≫
                  (extendDownNatToIntShiftXIso M.connesTotal 2 n).hom =
      M.underlying.iCycles n ≫ M.connesOrdinaryInclusion.f n := by
  let T : ChainComplex C ℕ := M.connesTotal
  let Q : ChainComplex C ℕ := cokernel (M.connesBicomplex.partialTotalι 0)
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) := partialTotalOuterEmbedding 2
  let U : ChainComplex C ℕ := T.extend E
  let e₀ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) :=
    ComplexShape.embeddingDownNatToIntShift 0
  let e₂ : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) :=
    ComplexShape.embeddingDownNatToIntShift 2
  let Qz : ChainComplex C ℤ := Q.extend e₀
  let Tz : ChainComplex C ℤ := T.extend e₂
  let Uz : ChainComplex C ℤ := U.extend e₀
  let N : Q ≅ U := M.connesTailNatIso
  let A : Uz ≅ Tz := extendNatAddIntIso T 2
  let F : Qz ≅ Tz := M.connesTailIso
  let j₀ : ℤ := 0 + ((n + 2 : ℕ) : ℤ)
  let j₂ : ℤ := 2 + (n : ℤ)
  have hj : j₀ = j₂ := by dsimp only [j₀, j₂]; omega
  have hz₀ : e₀.f (n + 2) = j₀ := rfl
  have hz₂ : e₀.f (n + 2) = j₂ := by
    change (0 : ℤ) + ((n + 2 : ℕ) : ℤ) = 2 + (n : ℤ)
    omega
  let q₀ : Qz.X j₀ ≅ Q.X (n + 2) := Q.extendXIso e₀ hz₀
  let q₂ : Qz.X j₂ ≅ Q.X (n + 2) := Q.extendXIso e₀ hz₂
  let u₂ : Uz.X j₂ ≅ U.X (n + 2) := U.extendXIso e₀ hz₂
  let t₂ : Tz.X j₂ ≅ T.X n := extendDownNatToIntShiftXIso T 2 n
  let eN : U.X (n + 2) ≅ T.X n := T.extendXIso E rfl
  let eD : Uz.X j₂ ≅ T.X n := extendNatAddIntRestrictionXIso T 2 n
  let eJ : Tz.X j₀ ≅ Tz.X j₂ := Tz.XIsoOfEq hj
  let f₂ : Q.X (n + 2) ⟶ U.X (n + 2) := N.hom.f (n + 2)
  let p₂ : T.X (n + 2) ⟶ Q.X (n + 2) :=
    (cokernel.π (M.connesBicomplex.partialTotalι 0)).f (n + 2)
  let s₂ : U.X (n + 2) ⟶ T.X (n + 2) := M.connesPeriodicitySectionF (n + 2)
  let r₂ : T.X (n + 2) ⟶ U.X (n + 2) := M.connesPeriodicityF (n + 2)
  let x₂ : M.underlying.cycles n ⟶ T.X (n + 2) := M.connesBoundaryLiftX₂ n
  let x₃ : M.underlying.cycles n ⟶ Q.X (n + 2) := M.connesBoundaryLiftX₃ n
  let z : M.underlying.cycles n ⟶ M.underlying.X n := M.underlying.iCycles n
  let i : M.underlying.X n ⟶ T.X n := M.connesOrdinaryInclusion.f n
  have hF : F.hom = extendMap N.hom e₀ ≫ A.hom := rfl
  have hD : eD = u₂ ≪≫ eN := rfl
  have hA : A.hom.f j₂ ≫ t₂.hom = u₂.hom ≫ eN.hom := by
    have h : A.hom.f j₂ = eD.hom ≫ t₂.inv := extendNatAddIntIso_hom_f T 2 n
    calc
      _ = (eD.hom ≫ t₂.inv) ≫ t₂.hom :=
        congrArg (fun f : Uz.X j₂ ⟶ Tz.X j₂ => f ≫ t₂.hom) h
      _ = eD.hom := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = u₂.hom ≫ eN.hom := congrArg (fun e : Uz.X j₂ ≅ T.X n => e.hom) hD
  have hExt : (extendMap N.hom e₀).f j₂ = q₂.hom ≫ f₂ ≫ u₂.inv :=
    extendMap_f N.hom e₀ hz₂
  have hF₂ : F.hom.f j₂ = (extendMap N.hom e₀).f j₂ ≫ A.hom.f j₂ :=
    congrArg (fun f : Qz ⟶ Tz => f.f j₂) hF
  have hCoordinate : q₂.inv ≫ F.hom.f j₂ ≫ t₂.hom = f₂ ≫ eN.hom := by
    calc
      _ = q₂.inv ≫ (extendMap N.hom e₀).f j₂ ≫ (A.hom.f j₂ ≫ t₂.hom) := by
        rw [hF₂]
        simp only [Category.assoc]
      _ = q₂.inv ≫ (q₂.hom ≫ f₂ ≫ u₂.inv) ≫ (u₂.hom ≫ eN.hom) := by rw [hExt, hA]
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hTransport : ∀ (z₀ z₂ : ℤ) (hz : z₀ = z₂)
      (h₀ : e₀.f (n + 2) = z₀) (h₂ : e₀.f (n + 2) = z₂),
      (Q.extendXIso e₀ h₀).inv ≫ F.hom.f z₀ ≫ (Tz.XIsoOfEq hz).hom =
        (Q.extendXIso e₀ h₂).inv ≫ F.hom.f z₂ := by
    intro z₀ z₂ hz h₀ h₂
    subst z₂
    change (Q.extendXIso e₀ h₀).inv ≫ F.hom.f z₀ ≫ 𝟙 _ = _
    rw [Category.comp_id]
  have hJ : q₀.inv ≫ F.hom.f j₀ ≫ eJ.hom = q₂.inv ≫ F.hom.f j₂ :=
    hTransport j₀ j₂ hj hz₀ hz₂
  have hp : p₂ ≫ f₂ = r₂ := M.cokernelπ_connesTailNatMap_f (n + 2)
  have hs : s₂ ≫ r₂ = 𝟙 (U.X (n + 2)) := M.connesPeriodicitySectionF_comp_periodicityF (n + 2)
  have hx₃ : x₃ = x₂ ≫ p₂ := rfl
  have hx₂ : x₂ = z ≫ i ≫ eN.inv ≫ s₂ := rfl
  change x₃ ≫ q₀.inv ≫ F.hom.f j₀ ≫ eJ.hom ≫ t₂.hom = z ≫ i
  calc
    _ = x₃ ≫ (q₀.inv ≫ F.hom.f j₀ ≫ eJ.hom) ≫ t₂.hom := by simp only [Category.assoc]
    _ = x₃ ≫ (q₂.inv ≫ F.hom.f j₂) ≫ t₂.hom :=
      congrArg (fun f : Q.X (n + 2) ⟶ Tz.X j₂ => x₃ ≫ f ≫ t₂.hom) hJ
    _ = x₃ ≫ (f₂ ≫ eN.hom) := by
      rw [Category.assoc, hCoordinate]
    _ = (x₂ ≫ p₂) ≫ (f₂ ≫ eN.hom) :=
      congrArg (fun f : M.underlying.cycles n ⟶ Q.X (n + 2) => f ≫ (f₂ ≫ eN.hom)) hx₃
    _ = x₂ ≫ (p₂ ≫ f₂) ≫ eN.hom := by simp only [Category.assoc]
    _ = x₂ ≫ r₂ ≫ eN.hom :=
      congrArg (fun f : T.X (n + 2) ⟶ U.X (n + 2) => x₂ ≫ f ≫ eN.hom) hp
    _ = (z ≫ i ≫ eN.inv ≫ s₂) ≫ r₂ ≫ eN.hom :=
      congrArg (fun f : M.underlying.cycles n ⟶ T.X (n + 2) => f ≫ r₂ ≫ eN.hom) hx₂
    _ = z ≫ i ≫ eN.inv ≫ (s₂ ≫ r₂) ≫ eN.hom := by simp only [Category.assoc]
    _ = z ≫ i := by
      rw [hs]
      simp only [Category.id_comp, Iso.inv_hom_id, Category.comp_id]

/-- The quotient cycle represents the original included cycle under the tail isomorphism. -/
@[reassoc]
theorem connesBoundaryTailCycle_comparison (n : ℕ) :
    M.connesBoundaryTailCycle n ≫ M.connesSBIPresentation.tailCyclesComparison n =
      cyclesMap M.connesOrdinaryInclusion n := by
  let D : ConnesSBIPresentation (A := C) := M.connesSBIPresentation
  let Q : ChainComplex C ℕ := D.shortComplex.X₃
  let T : ChainComplex C ℕ := D.shortComplex.X₂
  let Qz : ChainComplex C ℤ := Q.extend (ComplexShape.embeddingDownNatToIntShift 0)
  let Tz : ChainComplex C ℤ := T.extend (ComplexShape.embeddingDownNatToIntShift 2)
  let j₀ : ℤ := 0 + ((n + 2 : ℕ) : ℤ)
  let j₂ : ℤ := 2 + (n : ℤ)
  have hj : j₀ = j₂ := by dsimp only [j₀, j₂]; omega
  let q : Qz.X j₀ ≅ Q.X (n + 2) := Q.extendXIso (ComplexShape.embeddingDownNatToIntShift 0) rfl
  let d : Tz.X j₀ ≅ Tz.X j₂ := Tz.XIsoOfEq hj
  let t : Tz.X j₂ ≅ T.X n := extendDownNatToIntShiftXIso T 2 n
  let F : Qz ⟶ Tz := D.tailIso.hom
  let a : M.underlying.cycles n ⟶ Q.cycles (n + 2) := M.connesBoundaryTailCycle n
  let η : Q.cycles (n + 2) ⟶ T.cycles n := D.tailCyclesComparison n
  let κ : M.underlying.cycles n ⟶ Q.X (n + 2) := M.connesBoundaryLiftX₃ n
  let f : M.underlying ⟶ T := M.connesOrdinaryInclusion
  let g : M.underlying.cycles n ⟶ T.cycles n := cyclesMap f n
  have hη : η ≫ T.iCycles n =
      Q.iCycles (n + 2) ≫ q.inv ≫ F.f j₀ ≫ d.hom ≫ t.hom :=
    D.tailCyclesComparison_iCycles n
  have ha : a ≫ Q.iCycles (n + 2) = κ := M.connesBoundaryTailCycle_iCycles n
  have hg : g ≫ T.iCycles n = M.underlying.iCycles n ≫ f.f n := cyclesMap_i f n
  have hk : κ ≫ q.inv ≫ F.f j₀ ≫ d.hom ≫ t.hom =
      M.underlying.iCycles n ≫ f.f n := M.connesBoundaryLiftX₃_coordinates n
  change a ≫ η = g
  apply (cancel_mono (T.iCycles n)).1
  calc
    _ = a ≫ (η ≫ T.iCycles n) := Category.assoc _ _ _
    _ = a ≫ (Q.iCycles (n + 2) ≫ q.inv ≫ F.f j₀ ≫ d.hom ≫ t.hom) :=
      congrArg (fun f : Q.cycles (n + 2) ⟶ T.X n => a ≫ f) hη
    _ = (a ≫ Q.iCycles (n + 2)) ≫ (q.inv ≫ F.f j₀ ≫ d.hom ≫ t.hom) :=
      (Category.assoc _ _ _).symm
    _ = κ ≫ (q.inv ≫ F.f j₀ ≫ d.hom ≫ t.hom) :=
      congrArg (fun f : M.underlying.cycles n ⟶ Q.X (n + 2) =>
        f ≫ (q.inv ≫ F.f j₀ ≫ d.hom ≫ t.hom)) ha
    _ = M.underlying.iCycles n ≫ f.f n := hk
    _ = g ≫ T.iCycles n := hg.symm

/-- The lift represents I on the original homology class, with no comparison premise. -/
@[reassoc]
theorem connesBoundaryTailCycle_homologyπ (n : ℕ) :
    M.connesBoundaryTailCycle n ≫
        (cokernel (M.connesBicomplex.partialTotalι 0)).homologyπ (n + 2) ≫
          (M.connesSBIPresentation.tailHomologyIso n).hom =
      M.underlying.homologyπ n ≫ M.connesCyclicData.I n := by
  let D : ConnesSBIPresentation (A := C) := M.connesSBIPresentation
  let P : ChainComplex C ℕ := D.shortComplex.X₁
  let T : ChainComplex C ℕ := D.shortComplex.X₂
  let Q : ChainComplex C ℕ := D.shortComplex.X₃
  let c : M.underlying ⟶ P := M.connesFirstColumnMap
  let f : P ⟶ T := D.shortComplex.f
  let o : M.underlying ⟶ T := M.connesOrdinaryInclusion
  let h : M.underlying.homology n ≅ P.homology n := D.hIso n
  let e : Q.homology (n + 2) ≅ T.homology n := D.tailHomologyIso n
  let a : M.underlying.cycles n ⟶ Q.cycles (n + 2) := M.connesBoundaryTailCycle n
  let η : Q.cycles (n + 2) ⟶ T.cycles n := D.tailCyclesComparison n
  let I : M.underlying.homology n ⟶ T.homology n := M.connesCyclicData.I n
  have hIso : h.hom = homologyMap c n := by
    letI : IsIso c := M.connesFirstColumnMap_isIso
    change (isoOfQuasiIsoAt c n).hom = _
    exact isoOfQuasiIsoAt_hom c n
  have hI : I = homologyMap o n := by
    change h.hom ≫ homologyMap f n = homologyMap (c ≫ f) n
    calc
      _ = homologyMap c n ≫ homologyMap f n :=
        congrArg (fun g : M.underlying.homology n ⟶ P.homology n => g ≫ homologyMap f n) hIso
      _ = homologyMap (c ≫ f) n := (homologyMap_comp c f n).symm
  have hπ : Q.homologyπ (n + 2) ≫ e.hom = η ≫ T.homologyπ n :=
    D.homologyπ_tailHomologyIso_hom n
  have hComparison : a ≫ η = cyclesMap o n := M.connesBoundaryTailCycle_comparison n
  have hNat : M.underlying.homologyπ n ≫ homologyMap o n =
      cyclesMap o n ≫ T.homologyπ n := homologyπ_naturality o n
  change a ≫ Q.homologyπ (n + 2) ≫ e.hom = M.underlying.homologyπ n ≫ I
  calc
    _ = a ≫ (η ≫ T.homologyπ n) :=
      congrArg (fun f : Q.cycles (n + 2) ⟶ T.homology n => a ≫ f) hπ
    _ = (a ≫ η) ≫ T.homologyπ n := (Category.assoc _ _ _).symm
    _ = cyclesMap o n ≫ T.homologyπ n :=
      congrArg (fun f : M.underlying.cycles n ⟶ T.cycles n => f ≫ T.homologyπ n) hComparison
    _ = M.underlying.homologyπ n ≫ homologyMap o n := hNat.symm
    _ = M.underlying.homologyπ n ≫ I :=
      congrArg (fun f : M.underlying.homology n ⟶ T.homology n => M.underlying.homologyπ n ≫ f) hI.symm

/-- Native Snake/LES evaluates the tail lift as the B cycle in the first column. -/
@[reassoc]
theorem connesBoundaryTailCycle_δ (n : ℕ) :
    M.connesBoundaryTailCycle n ≫
        (cokernel (M.connesBicomplex.partialTotalι 0)).homologyπ (n + 2) ≫
          M.connesSBIPresentation.shortExact.δ (n + 2) (n + 1) (by rfl) =
      M.connesBoundaryFirstCycle n ≫
        (M.connesBicomplex.partialTotal 0).homologyπ (n + 1) := by
  let D : ConnesSBIPresentation (A := C) := M.connesSBIPresentation
  let S : ShortComplex (ChainComplex C ℕ) := D.shortComplex
  let T : ChainComplex C ℕ := S.X₂
  let P : ChainComplex C ℕ := S.X₁
  let Q : ChainComplex C ℕ := S.X₃
  let f : P ⟶ T := S.f
  let g : T ⟶ Q := S.g
  let x₂ : M.underlying.cycles n ⟶ T.X (n + 2) := M.connesBoundaryLiftX₂ n
  let x₃ : M.underlying.cycles n ⟶ Q.cycles (n + 2) := M.connesBoundaryTailCycle n
  let x₁ : M.underlying.cycles n ⟶ P.cycles (n + 1) := M.connesBoundaryFirstCycle n
  let y₂ : M.underlying.cycles n ⟶ T.opcycles (n + 2) := x₂ ≫ T.pOpcycles (n + 2)
  let y₃ : M.underlying.cycles n ⟶ Q.homology (n + 2) := x₃ ≫ Q.homologyπ (n + 2)
  let δ : Q.homology (n + 2) ⟶ P.homology (n + 1) := D.shortExact.δ (n + 2) (n + 1) rfl
  have hx : x₃ ≫ Q.iCycles (n + 2) = x₂ ≫ g.f (n + 2) := M.connesBoundaryTailCycle_iCycles n
  have h₂ : y₂ ≫ opcyclesMap g (n + 2) = y₃ ≫ Q.homologyι (n + 2) := by
    calc
      _ = x₂ ≫ (T.pOpcycles (n + 2) ≫ opcyclesMap g (n + 2)) := Category.assoc _ _ _
      _ = x₂ ≫ (g.f (n + 2) ≫ Q.pOpcycles (n + 2)) :=
        congrArg (fun f : T.X (n + 2) ⟶ Q.opcycles (n + 2) => x₂ ≫ f) (p_opcyclesMap g (n + 2))
      _ = (x₂ ≫ g.f (n + 2)) ≫ Q.pOpcycles (n + 2) := (Category.assoc _ _ _).symm
      _ = (x₃ ≫ Q.iCycles (n + 2)) ≫ Q.pOpcycles (n + 2) :=
        congrArg (fun f : M.underlying.cycles n ⟶ Q.X (n + 2) => f ≫ Q.pOpcycles (n + 2)) hx.symm
      _ = x₃ ≫ (Q.iCycles (n + 2) ≫ Q.pOpcycles (n + 2)) := Category.assoc _ _ _
      _ = x₃ ≫ (Q.homologyπ (n + 2) ≫ Q.homologyι (n + 2)) :=
        congrArg (fun f : Q.cycles (n + 2) ⟶ Q.opcycles (n + 2) => x₃ ≫ f)
          (HomologicalComplex.homology_π_ι (K := Q) (n + 2)).symm
      _ = y₃ ≫ Q.homologyι (n + 2) := (Category.assoc _ _ _).symm
  have hD : x₂ ≫ T.d (n + 2) (n + 1) =
      x₁ ≫ P.iCycles (n + 1) ≫ f.f (n + 1) := M.connesBoundaryLiftX₂_d n
  have h₁ : x₁ ≫ cyclesMap f (n + 1) = y₂ ≫ T.opcyclesToCycles (n + 2) (n + 1) := by
    apply (cancel_mono (T.iCycles (n + 1))).1
    have hf : cyclesMap f (n + 1) ≫ T.iCycles (n + 1) =
        P.iCycles (n + 1) ≫ f.f (n + 1) := HomologicalComplex.cyclesMap_i f (n + 1)
    have hop : T.pOpcycles (n + 2) ≫ T.opcyclesToCycles (n + 2) (n + 1) ≫
        T.iCycles (n + 1) = T.d (n + 2) (n + 1) := by
      rw [HomologicalComplex.opcyclesToCycles_iCycles, HomologicalComplex.p_fromOpcycles]
    calc
      _ = x₁ ≫ (cyclesMap f (n + 1) ≫ T.iCycles (n + 1)) := Category.assoc _ _ _
      _ = x₁ ≫ (P.iCycles (n + 1) ≫ f.f (n + 1)) :=
        congrArg (fun f : P.cycles (n + 1) ⟶ T.X (n + 1) => x₁ ≫ f) hf
      _ = x₂ ≫ T.d (n + 2) (n + 1) := hD.symm
      _ = x₂ ≫ (T.pOpcycles (n + 2) ≫ T.opcyclesToCycles (n + 2) (n + 1) ≫ T.iCycles (n + 1)) :=
        congrArg (fun f : T.X (n + 2) ⟶ T.X (n + 1) => x₂ ≫ f) hop.symm
      _ = (y₂ ≫ T.opcyclesToCycles (n + 2) (n + 1)) ≫ T.iCycles (n + 1) := by
        simp only [y₂, Category.assoc]
  have hd : y₃ ≫ δ = x₁ ≫ P.homologyπ (n + 1) :=
    D.shortExact.δ_eq' (n + 2) (n + 1) rfl y₃ y₂ x₁ h₂ h₁
  change x₃ ≫ Q.homologyπ (n + 2) ≫ δ = x₁ ≫ P.homologyπ (n + 1)
  calc
    _ = (x₃ ≫ Q.homologyπ (n + 2)) ≫ δ := (Category.assoc _ _ _).symm
    _ = x₁ ≫ P.homologyπ (n + 1) := hd

/-- I followed by the SBI connecting map is the original induced B operator. -/
@[reassoc]
theorem connes_I_comp_B_eq_homologyB (n : ℕ) :
    M.connesCyclicData.I n ≫ M.connesCyclicData.B n = M.homologyB n := by
  let D : ConnesSBIPresentation (A := C) := M.connesSBIPresentation
  let T : ChainComplex C ℕ := D.shortComplex.X₂
  let Q : ChainComplex C ℕ := D.shortComplex.X₃
  let P : ChainComplex C ℕ := D.shortComplex.X₁
  let e : Q.homology (n + 2) ≅ T.homology n := D.tailHomologyIso n
  let h : M.underlying.homology (n + 1) ≅ P.homology (n + 1) := D.hIso (n + 1)
  let π : M.underlying.cycles n ⟶ M.underlying.homology n := M.underlying.homologyπ n
  let I : M.underlying.homology n ⟶ T.homology n := D.I n
  let B : T.homology n ⟶ M.underlying.homology (n + 1) := D.B n
  let δ : Q.homology (n + 2) ⟶ P.homology (n + 1) := D.shortExact.δ (n + 2) (n + 1) rfl
  let x₃ : M.underlying.cycles n ⟶ Q.cycles (n + 2) := M.connesBoundaryTailCycle n
  let x₁ : M.underlying.cycles n ⟶ P.cycles (n + 1) := M.connesBoundaryFirstCycle n
  let ρ₃ : Q.cycles (n + 2) ⟶ Q.homology (n + 2) := Q.homologyπ (n + 2)
  let ρ₁ : P.cycles (n + 1) ⟶ P.homology (n + 1) := P.homologyπ (n + 1)
  let b₀ : M.underlying.cycles n ⟶ M.underlying.cycles (n + 1) := M.cyclesB n
  let c : M.underlying ⟶ P := M.connesFirstColumnMap
  have ht : π ≫ I = x₃ ≫ ρ₃ ≫ e.hom :=
    (M.connesBoundaryTailCycle_homologyπ n).symm
  have hi : (π ≫ I) ≫ e.inv = x₃ ≫ ρ₃ := by
    calc
      _ = ((x₃ ≫ ρ₃) ≫ e.hom) ≫ e.inv :=
        congrArg (fun f : M.underlying.cycles n ⟶ T.homology n => f ≫ e.inv)
          (ht.trans (Category.assoc x₃ ρ₃ e.hom).symm)
      _ = (x₃ ≫ ρ₃) ≫ (e.hom ≫ e.inv) := Category.assoc _ _ _
      _ = _ := by rw [e.hom_inv_id, Category.comp_id]
  have hIso : h.hom = homologyMap c (n + 1) := by
    letI : IsIso c := M.connesFirstColumnMap_isIso
    change (isoOfQuasiIsoAt c (n + 1)).hom = _
    exact isoOfQuasiIsoAt_hom c (n + 1)
  have hNat : cyclesMap c (n + 1) ≫ ρ₁ =
      M.underlying.homologyπ (n + 1) ≫ h.hom := by
    rw [hIso]
    exact (homologyπ_naturality c (n + 1)).symm
  have hFirst : x₁ = b₀ ≫ cyclesMap c (n + 1) := rfl
  have hb : (x₁ ≫ ρ₁) ≫ h.inv = b₀ ≫ M.underlying.homologyπ (n + 1) := by
    calc
      _ = ((b₀ ≫ cyclesMap c (n + 1)) ≫ ρ₁) ≫ h.inv :=
        congrArg (fun f : M.underlying.cycles n ⟶ P.cycles (n + 1) => (f ≫ ρ₁) ≫ h.inv) hFirst
      _ = (b₀ ≫ (cyclesMap c (n + 1) ≫ ρ₁)) ≫ h.inv :=
        congrArg (fun f : M.underlying.cycles n ⟶ P.homology (n + 1) => f ≫ h.inv)
          (Category.assoc b₀ (cyclesMap c (n + 1)) ρ₁)
      _ = (b₀ ≫ (M.underlying.homologyπ (n + 1) ≫ h.hom)) ≫ h.inv :=
        congrArg (fun f : M.underlying.cycles (n + 1) ⟶ P.homology (n + 1) => (b₀ ≫ f) ≫ h.inv) hNat
      _ = (b₀ ≫ M.underlying.homologyπ (n + 1)) ≫ (h.hom ≫ h.inv) := by
        simp only [Category.assoc]
      _ = _ := by rw [h.hom_inv_id, Category.comp_id]
  have hd₀ : x₃ ≫ ρ₃ ≫ δ = x₁ ≫ ρ₁ := M.connesBoundaryTailCycle_δ n
  have hd : (x₃ ≫ ρ₃) ≫ δ = x₁ ≫ ρ₁ := (Category.assoc _ _ _).trans hd₀
  have hB : B = e.inv ≫ δ ≫ h.inv := rfl
  apply (cancel_epi π).1
  change π ≫ (I ≫ B) = π ≫ M.homologyB n
  calc
    _ = (((π ≫ I) ≫ e.inv) ≫ δ) ≫ h.inv := by
      rw [hB]
      simp only [Category.assoc]
    _ = ((x₃ ≫ ρ₃) ≫ δ) ≫ h.inv :=
      congrArg (fun f : M.underlying.cycles n ⟶ Q.homology (n + 2) => (f ≫ δ) ≫ h.inv) hi
    _ = (x₁ ≫ ρ₁) ≫ h.inv :=
      congrArg (fun f : M.underlying.cycles n ⟶ P.homology (n + 1) => f ≫ h.inv) hd
    _ = b₀ ≫ M.underlying.homologyπ (n + 1) := hb
    _ = _ := (M.homologyπ_homologyB n).symm

end MixedComplex
