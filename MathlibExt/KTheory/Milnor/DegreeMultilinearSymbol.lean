/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.SymbolSlotLaws
public import MathlibExt.KTheory.Milnor.Naturality
public import MathlibExt.KTheory.Milnor.DegreeMap

/-!
# Multilinear Milnor symbol

For a field `F` and `n : ℕ`, the multilinear map
`symbolMultilinear F n :
  MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) (degree F n)`
sending `v` to the class of `[toMul v 0, …, toMul v (n-1)]` in `degree F n`.

The construction is the composite

```
(Additive Fˣ)^n -- PiTensorProduct.tprod -->
  TensorPower ℤ n (Additive Fˣ) -- TensorAlgebra.toDegree -->
    TensorRing.degree F n -- degreeLinear -->
      MilnorKRing.degree F n,
```

so `symbolTuple` is evaluation at `Additive.ofMul`.

This file also provides a robust bridge between the list/slot and
multilinear foundations: `symbolMultilinear_ofList` recovers the list
symbol from the multilinear evaluation, and
`symbolSlotHom_apply_eq_symbolMultilinear` expresses the fixed-slot
homomorphism as a degree-cast specialization of the multilinear symbol.

## Main results

* `symbolMultilinear_ofList` – evaluating `symbolMultilinear` on
  `i ↦ Additive.ofMul (xs.get i)` equals `symbolListDegree F xs`
* `symbolSlotHom_apply_eq_symbolMultilinear` – `symbolSlotHom` at `a`
  equals the appropriately degree-cast `symbolMultilinear` on
  `pref ++ [a] ++ suff`
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable (F : Type*) [Field F]
variable {K : Type*} [Field K]

private theorem symbolList_eq_prod_map (xs : List Fˣ) :
    symbolList F xs = (xs.map (symbol F)).prod := by
  induction xs with
  | nil => simp [symbolList_nil]
  | cons hd tl ih =>
    simp [symbolList_cons, ih, List.map_cons, List.prod_cons]

private theorem ofFn_symbol_eq_map (n : ℕ) (v : Fin n → Fˣ) :
    List.ofFn (fun i => symbol F (v i)) = (List.ofFn v).map (symbol F) := by
  apply List.ext_getElem
  · simp [List.length_ofFn]
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map]

private theorem prod_ofFn_symbol_eq_symbolList (n : ℕ) (v : Fin n → Fˣ) :
    (List.ofFn fun i => symbol F (v i)).prod = symbolList F (List.ofFn v) := by
  rw [ofFn_symbol_eq_map]
  exact (symbolList_eq_prod_map F (List.ofFn v)).symm

/-- Multilinear Milnor symbol via the tensor universal property. -/
noncomputable def symbolMultilinear (n : ℕ) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) (degree F n) :=
  ((degreeLinear F n).comp
      (TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n)).compMultilinearMap
    (PiTensorProduct.tprod ℤ (s := fun _ : Fin n => Additive Fˣ))

/-- Finite tuple symbol as evaluation of the multilinear symbol. -/
noncomputable def symbolTuple (n : ℕ) (v : Fin n → Fˣ) : degree F n :=
  symbolMultilinear F n (fun i => Additive.ofMul (v i))

private theorem toDegree_tprod_coe (n : ℕ) (v : Fin n → Fˣ) :
    (TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n
        (PiTensorProduct.tprod ℤ (s := fun _ : Fin n => Additive Fˣ)
          fun i => Additive.ofMul (v i)) : TensorRing F) =
      TensorAlgebra.tprod ℤ (Additive Fˣ) n fun i => Additive.ofMul (v i) := by
  simp [TensorAlgebra.toDegree, TensorPower.toTensorAlgebra_tprod]

private theorem mk_tprod_eq_symbolList (n : ℕ) (v : Fin n → Fˣ) :
    MilnorKRing.mk F
        (TensorAlgebra.tprod ℤ (Additive Fˣ) n fun i => Additive.ofMul (v i)) =
      symbolList F (List.ofFn v) := by
  have h_tprod : TensorAlgebra.tprod ℤ (Additive Fˣ) n
      (fun i => Additive.ofMul (v i)) =
      (List.ofFn fun i => TensorAlgebra.ι ℤ (Additive.ofMul (v i))).prod := by
    simp [TensorAlgebra.tprod_apply]
  calc MilnorKRing.mk F
        (TensorAlgebra.tprod ℤ (Additive Fˣ) n fun i => Additive.ofMul (v i))
      = MilnorKRing.mk F
          (List.ofFn fun i => TensorAlgebra.ι ℤ (Additive.ofMul (v i))).prod := by
        rw [h_tprod]
    _ = ((List.ofFn fun i => TensorAlgebra.ι ℤ (Additive.ofMul (v i))).map
          (MilnorKRing.mk F)).prod := by
        rw [map_list_prod]
    _ = (List.ofFn fun i => symbol F (v i)).prod := by
        have : (List.ofFn fun i => TensorAlgebra.ι ℤ (Additive.ofMul (v i))).map
            (MilnorKRing.mk F) =
            List.ofFn fun i => symbol F (v i) := by
          apply List.ext_getElem
          · simp [List.length_ofFn]
          · intro k hk1 hk2
            simp only [List.getElem_map, List.getElem_ofFn, symbol]
        rw [this]
    _ = symbolList F (List.ofFn v) := prod_ofFn_symbol_eq_symbolList F n v

/-- Coercion of `symbolTuple` to the Milnor ring equals the list symbol. -/
@[simp]
theorem symbolTuple_coe (n : ℕ) (v : Fin n → Fˣ) :
    (symbolTuple F n v : MilnorKRing F) = symbolList F (List.ofFn v) := by
  unfold symbolTuple symbolMultilinear
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
  have h_toDeg : (TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n
      (PiTensorProduct.tprod ℤ (s := fun _ : Fin n => Additive Fˣ)
        fun i => Additive.ofMul (v i)) : TensorRing F) =
      TensorAlgebra.tprod ℤ (Additive Fˣ) n fun i => Additive.ofMul (v i) :=
    toDegree_tprod_coe F n v
  calc (degreeLinear F n
        (TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n
          (PiTensorProduct.tprod ℤ (s := fun _ : Fin n => Additive Fˣ)
            fun i => Additive.ofMul (v i))) : MilnorKRing F)
      = MilnorKRing.mkLinear F
          (TensorAlgebra.toDegree (R := ℤ) (M := Additive Fˣ) n
            (PiTensorProduct.tprod ℤ (s := fun _ : Fin n => Additive Fˣ)
              fun i => Additive.ofMul (v i)) : TensorRing F) := by
        rw [degreeLinear_apply_coe]
    _ = MilnorKRing.mkLinear F
          (TensorAlgebra.tprod ℤ (Additive Fˣ) n fun i => Additive.ofMul (v i)) := by
        rw [h_toDeg]
    _ = MilnorKRing.mk F
          (TensorAlgebra.tprod ℤ (Additive Fˣ) n fun i => Additive.ofMul (v i)) := by
        rfl
    _ = symbolList F (List.ofFn v) := mk_tprod_eq_symbolList F n v

/-- Evaluation as `symbolTuple`. -/
theorem symbolMultilinear_apply (n : ℕ) (v : Fin n → Additive Fˣ) :
    symbolMultilinear F n v =
      degreeCastEquiv F (List.length_ofFn (f := fun i => Additive.toMul (v i)))
        (symbolListDegree F (List.ofFn fun i => Additive.toMul (v i))) := by
  apply Subtype.ext
  have h_coe : (symbolMultilinear F n v : MilnorKRing F) =
      symbolList F (List.ofFn fun i => Additive.toMul (v i)) := by
    have : v = fun i => Additive.ofMul (Additive.toMul (v i)) := by
      funext i; simp
    conv_lhs => rw [this]
    have h : symbolMultilinear F n
        (fun i => Additive.ofMul (Additive.toMul (v i))) =
        symbolTuple F n (fun i => Additive.toMul (v i)) := rfl
    rw [h]
    exact symbolTuple_coe F n (fun i => Additive.toMul (v i))
  calc (symbolMultilinear F n v : MilnorKRing F)
      = symbolList F (List.ofFn fun i => Additive.toMul (v i)) := h_coe
    _ = (symbolListDegree F (List.ofFn fun i => Additive.toMul (v i)) :
          MilnorKRing F) := by simp
    _ = (degreeCastEquiv F (List.length_ofFn (f := fun i => Additive.toMul (v i)))
          (symbolListDegree F (List.ofFn fun i => Additive.toMul (v i))) :
          MilnorKRing F) := by simp [degreeCastEquiv_val]

/-- Coercion of `symbolMultilinear` to the Milnor ring. -/
theorem symbolMultilinear_apply_coe (n : ℕ) (v : Fin n → Additive Fˣ) :
    (symbolMultilinear F n v : MilnorKRing F) =
      symbolList F (List.ofFn fun i => Additive.toMul (v i)) := by
  have h := symbolMultilinear_apply F n v
  calc (symbolMultilinear F n v : MilnorKRing F)
      = (degreeCastEquiv F (List.length_ofFn (f := fun i => Additive.toMul (v i)))
          (symbolListDegree F (List.ofFn fun i => Additive.toMul (v i))) :
          MilnorKRing F) := by rw [h]
    _ = symbolList F (List.ofFn fun i => Additive.toMul (v i)) := by
        simp [degreeCastEquiv_val, symbolListDegree_coe]

/-- `a * b` splits as sum in one coordinate via multilinearity. -/
theorem symbolMultilinear_map_mul {n : ℕ} (v : Fin n → Additive Fˣ) (i : Fin n)
    (a b : Fˣ) :
    symbolMultilinear F n (Function.update v i (Additive.ofMul (a * b))) =
      symbolMultilinear F n (Function.update v i (Additive.ofMul a)) +
      symbolMultilinear F n (Function.update v i (Additive.ofMul b)) := by
  have h_eq : Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b := by
    simp [ofMul_mul]
  rw [h_eq]
  exact (symbolMultilinear F n).map_update_add v i
    (Additive.ofMul a) (Additive.ofMul b)

/-- Power `a ^ c` is `c •` in one coordinate via multilinearity. -/
theorem symbolMultilinear_map_zsmul {n : ℕ} (v : Fin n → Additive Fˣ) (i : Fin n)
    (c : ℤ) (a : Fˣ) :
    symbolMultilinear F n (Function.update v i (Additive.ofMul (a ^ c))) =
      c • symbolMultilinear F n (Function.update v i (Additive.ofMul a)) := by
  have h_eq : Additive.ofMul (a ^ c) = c • Additive.ofMul a := by
    simp [ofMul_zpow]
  rw [h_eq]
  exact (symbolMultilinear F n).map_update_smul v i c (Additive.ofMul a)

/-- Unit `1` maps to zero in one coordinate. -/
theorem symbolMultilinear_map_one {n : ℕ} (v : Fin n → Additive Fˣ) (i : Fin n) :
    symbolMultilinear F n (Function.update v i (Additive.ofMul (1 : Fˣ))) = 0 := by
  have h_of : Additive.ofMul (1 : Fˣ) = (0 : Additive Fˣ) := by simp [ofMul_one]
  calc symbolMultilinear F n (Function.update v i (Additive.ofMul (1 : Fˣ)))
      = symbolMultilinear F n (Function.update v i (0 : Additive Fˣ)) := by rw [h_of]
    _ = 0 := (symbolMultilinear F n).map_update_zero v i

private theorem ofFn_eq_pair_take_drop {α : Type*} {n : ℕ} (v : Fin n → α)
    (i : Fin n) (hi : i.val + 1 < n) :
    let j : Fin n := ⟨i.val + 1, hi⟩
    List.ofFn v = (List.ofFn v).take i.val ++ [v i, v j] ++
      (List.ofFn v).drop (i.val + 2) := by
  intro j
  have h_len_i : i.val < (List.ofFn v).length := by
    simp [List.length_ofFn, i.is_lt]
  have h_len_j : i.val + 1 < (List.ofFn v).length := by
    simp [List.length_ofFn, hi]
  have h_drop_i : (List.ofFn v).drop i.val =
      (List.ofFn v)[i.val] :: (List.ofFn v).drop (i.val + 1) :=
    List.drop_eq_getElem_cons h_len_i
  have h_get_i : (List.ofFn v)[i.val] = v i := by
    simp [List.getElem_ofFn]
  have h_drop_j : (List.ofFn v).drop (i.val + 1) =
      (List.ofFn v)[i.val + 1] :: (List.ofFn v).drop (i.val + 2) :=
    List.drop_eq_getElem_cons h_len_j
  have h_get_j : (List.ofFn v)[i.val + 1] = v j := by
    simp [j, List.getElem_ofFn]
  calc List.ofFn v
      = (List.ofFn v).take i.val ++ (List.ofFn v).drop i.val := by
        rw [List.take_append_drop]
    _ = (List.ofFn v).take i.val ++
        ((List.ofFn v)[i.val] :: (List.ofFn v).drop (i.val + 1)) := by
        rw [h_drop_i]
    _ = (List.ofFn v).take i.val ++ (v i :: (List.ofFn v).drop (i.val + 1)) := by
        rw [h_get_i]
    _ = (List.ofFn v).take i.val ++
        (v i :: ((List.ofFn v)[i.val + 1] :: (List.ofFn v).drop (i.val + 2))) := by
        rw [h_drop_j]
    _ = (List.ofFn v).take i.val ++ (v i :: (v j :: (List.ofFn v).drop (i.val + 2))) := by
        rw [h_get_j]
    _ = (List.ofFn v).take i.val ++ ([v i, v j] ++ (List.ofFn v).drop (i.val + 2)) := by
        rfl
    _ = (List.ofFn v).take i.val ++ [v i, v j] ++ (List.ofFn v).drop (i.val + 2) := by
        rw [List.append_assoc]

/-- Adjacent Steinberg pair gives zero for `symbolTuple`. -/
theorem symbolTuple_steinberg {n : ℕ} (v : Fin n → Fˣ)
    (i : Fin n) (hi : i.val + 1 < n) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (h1 : v i = Units.mk0 a ha0)
    (h2 : v ⟨i.val + 1, hi⟩ =
      Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) :
    symbolTuple F n v = 0 := by
  have h_zero_coe : (symbolTuple F n v : MilnorKRing F) = 0 := by
    rw [symbolTuple_coe]
    have h_eq_pair := ofFn_eq_pair_take_drop (α := Fˣ) v i hi
    have h_list : List.ofFn v =
        (List.ofFn v).take i.val ++
          [Units.mk0 a ha0,
            Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)] ++
          (List.ofFn v).drop (i.val + 2) := by
      calc List.ofFn v
          = (List.ofFn v).take i.val ++ [v i, v ⟨i.val + 1, hi⟩] ++
            (List.ofFn v).drop (i.val + 2) := h_eq_pair
        _ = (List.ofFn v).take i.val ++
            [Units.mk0 a ha0,
              Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)] ++
            (List.ofFn v).drop (i.val + 2) := by rw [h1, h2]
    rw [h_list]
    exact symbolList_steinberg_middle F _ _ a ha0 ha1
  have h_val_eq : (symbolTuple F n v).val = (0 : degree F n).val := by
    calc (symbolTuple F n v).val
        = (symbolTuple F n v : MilnorKRing F) := rfl
      _ = 0 := h_zero_coe
      _ = (0 : degree F n).val := by simp
  exact Subtype.ext h_val_eq

/-- Adjacent Steinberg pair gives zero for `symbolMultilinear`. -/
theorem symbolMultilinear_steinberg {n : ℕ} (v : Fin n → Additive Fˣ)
    (i : Fin n) (hi : i.val + 1 < n) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (h1 : Additive.toMul (v i) = Units.mk0 a ha0)
    (h2 : Additive.toMul (v ⟨i.val + 1, hi⟩) =
      Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) :
    symbolMultilinear F n v = 0 := by
  have h_eq : v = fun j => Additive.ofMul (Additive.toMul (v j)) := by
    funext j; simp
  conv_lhs => rw [h_eq]
  have h_tuple : symbolMultilinear F n
      (fun j => Additive.ofMul (Additive.toMul (v j))) =
      symbolTuple F n (fun j => Additive.toMul (v j)) := rfl
  rw [h_tuple]
  exact symbolTuple_steinberg F _ i hi a ha0 ha1 h1 h2

/-- Naturality of `symbolTuple` under a ring homomorphism. -/
theorem symbolTuple_mapDegree (f : F →+* K) (n : ℕ) (v : Fin n → Fˣ) :
    mapDegree f n (symbolTuple F n v) =
      symbolTuple K n (fun i => Units.map f.toMonoidHom (v i)) := by
  apply Subtype.ext
  have h_map : (List.ofFn v).map (Units.map f.toMonoidHom) =
      List.ofFn (fun i => Units.map f.toMonoidHom (v i)) := by
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      simp
  calc (mapDegree f n (symbolTuple F n v) : MilnorKRing K)
      = map f (symbolTuple F n v : MilnorKRing F) := by simp [mapDegree_apply]
    _ = map f (symbolList F (List.ofFn v)) := by simp [symbolTuple_coe]
    _ = symbolList K ((List.ofFn v).map (Units.map f.toMonoidHom)) := by
        rw [map_symbolList]
    _ = symbolList K (List.ofFn fun i => Units.map f.toMonoidHom (v i)) := by
        rw [h_map]
    _ = (symbolTuple K n fun i => Units.map f.toMonoidHom (v i) :
          MilnorKRing K) := by simp [symbolTuple_coe]

/-- Naturality of `symbolMultilinear` under a ring homomorphism. -/
theorem symbolMultilinear_mapDegree (f : F →+* K) (n : ℕ)
    (v : Fin n → Additive Fˣ) :
    mapDegree f n (symbolMultilinear F n v) =
      symbolMultilinear K n (fun i => unitsAddHom f (v i)) := by
  have h_toMul : ∀ i,
      Additive.toMul (unitsAddHom f (v i)) =
        Units.map f.toMonoidHom (Additive.toMul (v i)) := by
    intro i; simp [unitsAddHom]
  have h_eq : (fun i => Units.map f.toMonoidHom (Additive.toMul (v i))) =
      (fun i => Additive.toMul (unitsAddHom f (v i))) := by
    funext i; rw [h_toMul]
  have h1 : mapDegree f n (symbolTuple F n fun i => Additive.toMul (v i)) =
      symbolTuple K n fun i => Units.map f.toMonoidHom (Additive.toMul (v i)) :=
    symbolTuple_mapDegree F f n (fun i => Additive.toMul (v i))
  have h2 : symbolTuple K n (fun i => Units.map f.toMonoidHom
      (Additive.toMul (v i))) =
      symbolTuple K n (fun i => Additive.toMul (unitsAddHom f (v i))) := by rw [h_eq]
  calc mapDegree f n (symbolMultilinear F n v)
      = mapDegree f n (symbolTuple F n fun i => Additive.toMul (v i)) := by
        have : v = fun i => Additive.ofMul (Additive.toMul (v i)) := by
          funext i; simp
        conv_lhs => rw [this]
        rfl
    _ = symbolTuple K n fun i => Units.map f.toMonoidHom
          (Additive.toMul (v i)) := h1
    _ = symbolTuple K n fun i => Additive.toMul (unitsAddHom f (v i)) := h2
    _ = symbolMultilinear K n fun i => unitsAddHom f (v i) := rfl

/-- Bridge from list symbols to the multilinear symbol: evaluating
`symbolMultilinear` on `i ↦ Additive.ofMul (xs.get i)` recovers
`symbolListDegree`. -/
theorem symbolMultilinear_ofList (xs : List Fˣ) :
    symbolMultilinear F xs.length (fun i => Additive.ofMul (xs.get i)) =
      symbolListDegree F xs := by
  have h_base := symbolMultilinear_apply F xs.length
      (fun i : Fin xs.length => Additive.ofMul (xs.get i))
  have h_fun : (fun i : Fin xs.length =>
      Additive.toMul (Additive.ofMul (xs.get i))) =
      fun i : Fin xs.length => xs.get i := by
    funext i; simp
  rw [h_fun] at h_base
  rw [h_base]
  apply Subtype.ext
  rw [degreeCastEquiv_val]
  have h_ofFn : List.ofFn (fun i : Fin xs.length => xs.get i) = xs :=
    List.ofFn_get xs
  calc (symbolListDegree F (List.ofFn fun i : Fin xs.length => xs.get i) :
          MilnorKRing F)
      = symbolList F (List.ofFn fun i : Fin xs.length => xs.get i) := by
        simp
    _ = symbolList F xs := by rw [h_ofFn]
    _ = (symbolListDegree F xs : MilnorKRing F) := by simp

/-- Fixed-slot specialization as a degree-cast multilinear evaluation:
`symbolSlotHom` at `a` equals the appropriately degree-cast value of
`symbolMultilinear` on `pref ++ [a] ++ suff`. -/
theorem symbolSlotHom_apply_eq_symbolMultilinear
    (pref suff : List Fˣ) (a : Fˣ) :
    symbolSlotHom F pref suff (Additive.ofMul a) =
      degreeCastEquiv F (symbolSlotDegree_eq_length F pref suff a).symm
        (symbolMultilinear F (pref ++ [a] ++ suff).length
          (fun i => Additive.ofMul ((pref ++ [a] ++ suff).get i))) := by
  calc symbolSlotHom F pref suff (Additive.ofMul a)
      = symbolSlotDegreeElement F pref suff a := symbolSlotHom_apply F pref suff a
    _ = degreeCastEquiv F (symbolSlotDegree_eq_length F pref suff a).symm
          (symbolListDegree F (pref ++ [a] ++ suff)) := rfl
    _ = degreeCastEquiv F (symbolSlotDegree_eq_length F pref suff a).symm
          (symbolMultilinear F (pref ++ [a] ++ suff).length
            (fun i => Additive.ofMul ((pref ++ [a] ++ suff).get i))) := by
          rw [← symbolMultilinear_ofList]

end MilnorKRing
end MilnorK
