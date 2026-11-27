/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.MixedComplex.Connes
public import MathlibExt.Algebra.Homology.ChainComplex.MixedBicomplex
public import MathlibExt.Algebra.Homology.Embedding.Composition
public import MathlibExt.Algebra.Homology.PartialTotalZero
public import MathlibExt.Algebra.Homology.HomologicalBicomplex.TotalDiagram

/-!
# The Connes bicomplex of a mixed complex

The mixed-complex identities give a homotopy from zero to zero whose
degree-one components are B. Its signed columns construct the Connes
bicomplex and identify its components and differentials.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace MixedComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] (M : MixedComplex C)

/-- The original mixed operator, with only its relevant degree equality transported. -/
def operatorFamily (i j : ℕ) (h : (ComplexShape.down ℕ).Rel j i) :
    M.underlying.X i ⟶ M.underlying.X j :=
  M.B i ≫ (M.underlying.XIsoOfEq (show i + 1 = j from h)).hom

/-- The mixed identities say exactly that the native boundary sum of B is zero. -/
theorem operatorFamily_nullMap_zero : Homotopy.nullHomotopicMap' M.operatorFamily = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left (k₁ := 1) (k₀ := 0)
      (by rfl) (by intro l; simp [ComplexShape.down_Rel]) M.operatorFamily]
    simp only [operatorFamily, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id, HomologicalComplex.zero_f]
    exact M.B_b_zero
  | succ n =>
    rw [Homotopy.nullHomotopicMap'_f (k₂ := n + 1 + 1) (k₁ := n + 1) (k₀ := n)
      (by rfl) (by rfl) M.operatorFamily]
    simp only [operatorFamily, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
      Category.comp_id, HomologicalComplex.zero_f]
    exact (add_comm _ _).trans (M.anticomm n)

/-- The mixed operator is the relevant component of a native zero homotopy. -/
def boundaryHomotopy : Homotopy (0 : M.underlying ⟶ M.underlying) 0 :=
  (Homotopy.ofEq M.operatorFamily_nullMap_zero.symm).trans
    (Homotopy.nullHomotopy' M.operatorFamily)

/-- Every relevant component is exactly the original mixed operator. -/
@[simp]
theorem boundaryHomotopy_hom (n : ℕ) : (M.boundaryHomotopy).hom n (n + 1) = M.B n := by
  dsimp only [boundaryHomotopy, Homotopy.trans, Homotopy.ofEq,
    Homotopy.nullHomotopy', Homotopy.nullHomotopy]
  simp only [Pi.add_apply, Pi.zero_apply,
    dif_pos (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n),
    operatorFamily, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, zero_add]

section HomologyOperator

variable (n : ℕ) [M.underlying.HasHomology n] [M.underlying.HasHomology (n + 1)]

/-- The original B operator maps the cycle object in each relevant degree. -/
def cyclesB : M.underlying.cycles n ⟶ M.underlying.cycles (n + 1) :=
  M.boundaryHomotopy.cyclesDegreeMap (by rfl)

/-- The cycle map keeps the B component under the original cycle inclusion. -/
@[reassoc]
theorem cyclesB_iCycles : M.cyclesB n ≫ M.underlying.iCycles (n + 1) =
    M.underlying.iCycles n ≫ M.B n := by
  simpa only [cyclesB, boundaryHomotopy_hom] using
    M.boundaryHomotopy.cyclesDegreeMap_i (i := n) (j := n + 1)
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)

/-- The original B component sends every actual source cycle to a target cycle. -/
theorem iCycles_B_d : (M.underlying.iCycles n ≫ M.B n) ≫ M.underlying.d (n + 1) n = 0 := by
  rw [← M.cyclesB_iCycles n, Category.assoc, M.underlying.iCycles_d, comp_zero]

/-- Original boundaries are killed after the B cycle map and the target class projection. -/
@[reassoc]
theorem toCycles_cyclesB_homologyπ :
    M.underlying.toCycles (n + 1) n ≫ M.cyclesB n ≫ M.underlying.homologyπ (n + 1) = 0 :=
  M.boundaryHomotopy.toCycles_cyclesDegreeMap_homologyπ_eq_zero
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)

/-- The degree-one operator descends to the existing original homology objects. -/
def homologyB : M.underlying.homology n ⟶ M.underlying.homology (n + 1) :=
  M.boundaryHomotopy.homologyDegreeMap (by rfl)

/-- The B homology operator is characterized by its original cycle classes. -/
@[reassoc]
theorem homologyπ_homologyB : M.underlying.homologyπ n ≫ M.homologyB n =
    M.cyclesB n ≫ M.underlying.homologyπ (n + 1) :=
  M.boundaryHomotopy.homologyπ_homologyDegreeMap
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)

/-- Original component square-zero gives square-zero on the homology objects. -/
theorem homologyB_comp [M.underlying.HasHomology (n + 2)] :
    M.homologyB n ≫ M.homologyB (n + 1) = 0 :=
  M.boundaryHomotopy.homologyDegreeMap_comp_eq_zero
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)
    (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1)) M.boundaryHomotopy
    (by simpa only [boundaryHomotopy_hom] using M.B_sq n)

variable {N : MixedComplex C} [N.underlying.HasHomology n]
  [N.underlying.HasHomology (n + 1)]

/-- Every original mixed-complex morphism intertwines B on its actual cycle objects. -/
@[reassoc]
theorem cyclesB_naturality (f : M ⟶ N) :
    HomologicalComplex.cyclesMap f.underlying n ≫ N.cyclesB n =
      M.cyclesB n ≫ HomologicalComplex.cyclesMap f.underlying (n + 1) :=
  M.boundaryHomotopy.cyclesDegreeMap_naturality_square
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) N.boundaryHomotopy
    f.underlying f.underlying (by simpa only [boundaryHomotopy_hom] using f.comm_B n)

/-- The B action on actual mixed homology is natural for every original mixed-complex map. -/
@[reassoc]
theorem homologyB_naturality (f : M ⟶ N) :
    HomologicalComplex.homologyMap f.underlying n ≫ N.homologyB n =
      M.homologyB n ≫ HomologicalComplex.homologyMap f.underlying (n + 1) :=
  M.boundaryHomotopy.homologyDegreeMap_naturality_square
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) N.boundaryHomotopy
    f.underlying f.underlying (by simpa only [boundaryHomotopy_hom] using f.comm_B n)

end HomologyOperator

variable [HasZeroObject C]

/-- The Connes bicomplex built from the original b and B maps. -/
def connesBicomplex : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.mixedBicomplex M.underlying M.boundaryHomotopy
    (fun n => by simpa only [boundaryHomotopy_hom] using M.B_sq n)

/-- Original supporting-triangle cells have their actual native degree coordinates. -/
def connesBicomplexCellIso (p q : ℕ) (h : p ≤ q) :
    ((M.connesBicomplex).X p).X q ≅ M.underlying.X (q - p) :=
  ChainComplex.mixedBicomplexCellIso M.underlying M.boundaryHomotopy
    (fun n => by simpa only [boundaryHomotopy_hom] using M.B_sq n) p q h

/-- The mixed construction has native zero cells outside its actual supporting triangle. -/
theorem connesBicomplex_isZero_cell (p q : ℕ) (h : q < p) :
    IsZero (((M.connesBicomplex).X p).X q) :=
  ChainComplex.mixedBicomplex_isZero_cell M.underlying M.boundaryHomotopy
    (fun n => by simpa only [boundaryHomotopy_hom] using M.B_sq n) p q h

/-- The component-characterized Connes data are constructed from the mixed complex. -/
def connesDoubleData : ConnesDoubleData M where
  K := M.connesBicomplex
  objIso := M.connesBicomplexCellIso
  isZero := M.connesBicomplex_isZero_cell
  vertical_spec p q h h' := by
    let e := ChainComplex.mixedColumnIso M.underlying p (q - p) q (Nat.sub_add_cancel h)
    let e' := ChainComplex.mixedColumnIso M.underlying p ((q + 1) - p) (q + 1)
      (Nat.sub_add_cancel h')
    have hD := ChainComplex.mixedColumn_d_eq M.underlying p ((q + 1) - p) (q - p)
      (q + 1) q (Nat.sub_add_cancel h') (Nat.sub_add_cancel h)
    have hEq : (q + 1) - p = (q - p) + 1 := by omega
    have hX : eqToHom (congrArg M.underlying.X hEq) ≫
        M.underlying.d ((q - p) + 1) (q - p) =
      M.underlying.d ((q + 1) - p) (q - p) :=
      M.underlying.XIsoOfEq_hom_comp_d hEq (q - p)
    have hCol : (ChainComplex.mixedColumn M.underlying p).d (q + 1) q ≫ e.hom =
        e'.hom ≫ ((-1 : ℤ) ^ p • M.underlying.d ((q + 1) - p) (q - p)) := by
      rw [hD]
      change (e'.hom ≫ (((-1 : ℤˣ) ^ p) •
          M.underlying.d ((q + 1) - p) (q - p)) ≫ e.inv) ≫ e.hom =
        e'.hom ≫ ((-1 : ℤ) ^ p • M.underlying.d ((q + 1) - p) (q - p))
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    change e'.hom ≫ eqToHom (congrArg M.underlying.X hEq) ≫
        ((-1 : ℤ) ^ p • M.underlying.d ((q - p) + 1) (q - p)) =
      (ChainComplex.mixedColumn M.underlying p).d (q + 1) q ≫ e.hom
    rw [hCol, Preadditive.comp_zsmul, hX]
  horizontal_spec p q h h' := by
    let e := ChainComplex.mixedColumnIso M.underlying p (q - p) q (Nat.sub_add_cancel h')
    let e' := ChainComplex.mixedColumnIso M.underlying (p + 1) (q - (p + 1)) q
      (Nat.sub_add_cancel h)
    let a := ChainComplex.mixedColumnIso M.underlying p (q - (p + 1) + 1) q (by omega)
    have hEq : q - (p + 1) + 1 = q - p := by omega
    have hCoordinates : ∀ (i j : ℕ) (hi : i + p = q) (hj : j + p = q) (hij : i = j),
        (ChainComplex.mixedColumnIso M.underlying p i q hi).inv ≫
          (ChainComplex.mixedColumnIso M.underlying p j q hj).hom =
            eqToHom (congrArg M.underlying.X hij) := by
      intro i j hi hj hij
      cases hij
      simp only [eqToHom_refl, Iso.inv_hom_id]
    have hE : a.inv ≫ e.hom = eqToHom (congrArg M.underlying.X hEq) :=
      hCoordinates (q - (p + 1) + 1) (q - p) (by omega) (Nat.sub_add_cancel h') hEq
    have hMap : ChainComplex.mixedHorizontalComponent M.underlying M.boundaryHomotopy p q =
        e'.hom ≫ M.B (q - (p + 1)) ≫ a.inv := by
      simpa only [boundaryHomotopy_hom] using
        (ChainComplex.mixedHorizontalComponent_eq M.underlying M.boundaryHomotopy p
          (q - (p + 1)) q (Nat.sub_add_cancel h))
    have hHorizontal : (M.connesBicomplex.d (p + 1) p).f q =
        ChainComplex.mixedHorizontalComponent M.underlying M.boundaryHomotopy p q := by
      dsimp only [connesBicomplex, ChainComplex.mixedBicomplex]
      rw [ChainComplex.of_d, ChainComplex.mixedHorizontalMap_f]
    rw [hHorizontal]
    change e'.hom ≫ M.B (q - (p + 1)) ≫ eqToHom (congrArg M.underlying.X hEq) =
      ChainComplex.mixedHorizontalComponent M.underlying M.boundaryHomotopy p q ≫ e.hom
    rw [hMap]
    simpa only [Category.assoc] using
      (congrArg (fun f : M.underlying.X (q - (p + 1) + 1) ⟶ M.underlying.X (q - p) =>
        e'.hom ≫ M.B (q - (p + 1)) ≫ f) hE).symm

/-- Every original mixed-complex map gives the map of the constructed Connes bicomplexes. -/
def connesBicomplexMap {N : MixedComplex C} (f : M ⟶ N) : M.connesBicomplex ⟶ N.connesBicomplex :=
  ChainComplex.mixedBicomplexMap f.underlying N.boundaryHomotopy
    (fun n => by simpa only [boundaryHomotopy_hom] using N.B_sq n)
    (fun n => by simpa only [boundaryHomotopy_hom] using f.comm_B n)

/-- The mixed-complex map keeps every original extended chain-map component. -/
@[simp]
theorem connesBicomplexMap_f {N : MixedComplex C} (f : M ⟶ N) (p : ℕ) :
    (M.connesBicomplexMap f).f p = ChainComplex.mixedColumnMap f.underlying p := rfl

/-- Identity mixed-complex maps retain the identity of each actual signed column. -/
@[simp]
theorem connesBicomplexMap_id : M.connesBicomplexMap (𝟙 M) = 𝟙 M.connesBicomplex := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  change (ChainComplex.mixedColumnMap (𝟙 M.underlying) p).f q = 𝟙 _
  by_cases h : p ≤ q
  · have hMap := ChainComplex.mixedColumnMap_f_eq (𝟙 M.underlying) p (q - p) q
      (Nat.sub_add_cancel h)
    simpa only [HomologicalComplex.id_f, Category.id_comp, Category.comp_id,
      Iso.hom_inv_id] using hMap
  · exact (ChainComplex.mixedColumn_isZero M.underlying p q (by omega)).eq_of_src _ _

/-- The constructed bicomplex keeps the composition of the original mixed-complex maps. -/
@[reassoc]
theorem connesBicomplexMap_comp {N P : MixedComplex C} (f : M ⟶ N) (g : N ⟶ P) :
    M.connesBicomplexMap (f ≫ g) = M.connesBicomplexMap f ≫ N.connesBicomplexMap g := by
  apply HomologicalComplex.hom_ext
  intro p
  change ChainComplex.mixedColumnMap (f.underlying ≫ g.underlying) p =
    ChainComplex.mixedColumnMap f.underlying p ≫ ChainComplex.mixedColumnMap g.underlying p
  exact ChainComplex.mixedColumnMap_comp f.underlying g.underlying p

/-- The (b,B)-bicomplex construction is functorial on all original mixed-complex maps. -/
def connesBicomplexFunctor : MixedComplex C ⥤
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  obj M := M.connesBicomplex
  map f := connesBicomplexMap _ f
  map_id M := M.connesBicomplexMap_id
  map_comp f g := connesBicomplexMap_comp _ f g

end MixedComplex

namespace MixedComplex

universe u v

section ActualTotal

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (M : MixedComplex C) [M.connesBicomplex.HasTotal (ComplexShape.down ℕ)]

/-- The original mixed complex has its actual finite-diagonal Connes total. -/
abbrev connesTotal : ChainComplex C ℕ := M.connesBicomplex.total (ComplexShape.down ℕ)

end ActualTotal

variable {C : Type u} [Category.{v} C] [Abelian C] (M : MixedComplex C)

/-- The Connes totalization retains every original mixed-complex map. -/
def connesTotalFunctor : MixedComplex C ⥤ ChainComplex C ℕ :=
  HomologicalComplex₂.totalDiagram connesBicomplexFunctor (ComplexShape.down ℕ)

/-- Ordinary cyclic homology of a mixed complex is the homology of its constructed total. -/
def connesHomologyFunctor (n : ℕ) : MixedComplex C ⥤ C :=
  connesTotalFunctor ⋙ HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n

/-- The zeroth partial total is the signed row zero, with the native row quotient as hom. -/
def connesFirstColumnRowIso : M.connesBicomplex.partialTotal 0 ≅ M.connesBicomplex.totalRow 0 := by
  let B := M.connesBicomplex
  letI : IsIso (B.partialTotalRowQuotient 0) :=
    B.partialTotalZeroShortExact.isIso_g_iff.mpr (isZero_zero _)
  exact asIso (B.partialTotalRowQuotient 0)

/-- The original mixed chain complex is recovered from the first column of its Connes total. -/
def connesFirstColumnIso : M.connesBicomplex.partialTotal 0 ≅ M.underlying :=
  M.connesFirstColumnRowIso ≪≫ M.connesBicomplex.totalRowZeroIso ≪≫
    ChainComplex.mixedColumnZeroIso M.underlying

/-- The original-column comparison is a chain isomorphism, so its quasi-isomorphism
does not need to be supplied to the mixed cyclic construction. -/
def connesFirstColumnMap : M.underlying ⟶ M.connesBicomplex.partialTotal 0 :=
  M.connesFirstColumnIso.inv

/-- The first-column map is the inverse of the native column isomorphism. -/
instance connesFirstColumnMap_isIso : IsIso M.connesFirstColumnMap := by
  unfold connesFirstColumnMap
  infer_instance

/-- The first-column map has the original coprojection coordinates.
This supplies the column comparison required by generic mixed cyclic data. -/
theorem connesFirstColumnMap_spec (q : ℕ) :
    (M.connesFirstColumnMap).f q = genericMixedColumnιComponent M.connesDoubleData q := by
  let B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
    M.connesBicomplex
  let P : ChainComplex C ℕ := B.partialTotal 0
  let R₀ : ChainComplex C ℕ := B.totalRow 0
  let C₀ : ChainComplex C ℕ := B.X 0
  let e : P ≅ R₀ := M.connesFirstColumnRowIso
  let a : R₀ ≅ C₀ := B.totalRowZeroIso
  let b : C₀ ≅ M.underlying := ChainComplex.mixedColumnZeroIso M.underlying
  let E : P ≅ M.underlying := M.connesFirstColumnIso
  let V : ChainComplex C ℕ ⥤ C := HomologicalComplex.eval C (ComplexShape.down ℕ) q
  let e₀ : P.X q ≅ R₀.X q := V.mapIso (X := P) (Y := R₀) e
  let a₀ : R₀.X q ≅ C₀.X q := V.mapIso (X := R₀) (Y := C₀) a
  let b₀ : C₀.X q ≅ M.underlying.X q :=
    V.mapIso (X := C₀) (Y := M.underlying) b
  let r₀ : R₀.X q ≅ C₀.X q := B.totalRowXIso 0 q q (Nat.zero_add q)
  let c₀ : C₀.X q ≅ M.underlying.X q :=
    ChainComplex.mixedColumnIso M.underlying 0 q q rfl
  let c : C₀.X q ≅ M.underlying.X q :=
    (M.connesDoubleData.objIso 0 q (Nat.zero_le q)) ≪≫
      eqToIso (congrArg (mixedObject M) (Nat.sub_zero q))
  let i : C₀.X q ⟶ P.X q :=
    B.partialTotalComponent 0 (0 : Fin 1) q q (Nat.zero_add q)
  have hE : E = e ≪≫ a ≪≫ b := rfl
  have hV : V.mapIso (X := P) (Y := M.underlying) E = e₀ ≪≫ a₀ ≪≫ b₀ := by
    rw [hE, Functor.mapIso_trans, Functor.mapIso_trans]
  have hInv : E.inv.f q = b₀.inv ≫ a₀.inv ≫ e₀.inv := by
    have h : V.map (X := M.underlying) (Y := P) E.inv =
        b₀.inv ≫ a₀.inv ≫ e₀.inv := by
      simpa only [Functor.mapIso_inv, Iso.trans_inv, Category.assoc] using
        congrArg (fun f : P.X q ≅ M.underlying.X q => f.inv) hV
    change E.inv.f q = b₀.inv ≫ a₀.inv ≫ e₀.inv at h
    exact h
  have hCell : c = c₀ := by
    change c₀ ≪≫ Iso.refl (M.underlying.X q) = c₀
    exact Iso.trans_refl c₀
  have hColumn : b₀ = c₀ := by
    apply Iso.ext
    change (V.mapIso (X := C₀) (Y := M.underlying) b).hom = c₀.hom
    rw [Functor.mapIso_hom]
    change b.hom.f q = c₀.hom
    exact ChainComplex.mixedColumnZeroIso_hom_f M.underlying q
  have hRow : a₀.inv = r₀.inv :=
    HomologicalComplex₂.totalRowZeroIso_inv_f B q
  have he : e₀.hom = (B.partialTotalRowQuotient 0).f q := rfl
  have hQuotient : i ≫ e₀.hom = r₀.inv := by
    rw [he]
    exact B.partialTotalComponent_comp_partialTotalRowQuotient 0 q q (Nat.zero_add q)
  have hi : i = a₀.inv ≫ e₀.inv := by
    apply (cancel_mono e₀.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      hQuotient.trans hRow.symm
  have hGeneric :
      (genericMixedColumnιComponent M.connesDoubleData q : M.underlying.X q ⟶ P.X q) =
        c.inv ≫ i := by
    change c₀.inv ≫ i = (c₀ ≪≫ Iso.refl (M.underlying.X q)).inv ≫ i
    simp only [Iso.trans_inv, Iso.refl_inv, Category.id_comp]
  change E.inv.f q = _
  rw [hGeneric, hInv, hCell, ← hColumn, hi]

end MixedComplex
