/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.IdealCountFaces
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Adjacent ideal-block faces in tensor words

Native tensor associators place an ideal block between arbitrary prefix and
suffix tensor words. The native ideal inclusion and tensor concatenation
retain the original entry values and order. Every internal ideal face agrees
with the ambient adjacent face at its corresponding position.

These generic maps and equations depend only on the ground ring, algebra,
native two-sided subalgebra, coefficient and word lengths. They use the
tensor and face constructions.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w z

namespace ModuleCat.Algebra.Hochschild.NonUnital

private theorem originalTensorPowerMul_tprod (k : Type u) [CommRing k]
    (M : Type v) [AddCommGroup M] [Module k M] {left right : ℕ}
    (a : Fin left → M) (b : Fin right → M) :
    (TensorPower.mulEquiv : TensorPower k left M ⊗[k] TensorPower k right M ≃ₗ[k]
        TensorPower k (left + right) M)
      (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) =
      PiTensorProduct.tprod k (Fin.append a b) :=
  TensorPower.tprod_mul_tprod k a b

private theorem originalContextTensor_ext (k : Type u) [CommRing k]
    (A J : Type v) [AddCommGroup A] [Module k A] [AddCommGroup J] [Module k J]
    (V : Type w) [AddCommGroup V] [Module k V]
    {E : Type z} [AddCommGroup E] [Module k E] {left right m : ℕ}
    (f g : (V ⊗[k] (TensorPower k left A ⊗[k] TensorPower k right A)) ⊗[k]
        TensorPower k m J →ₗ[k] E)
    (h : ∀ (v : V) (a : Fin left → A) (b : Fin right → A) (c : Fin m → J),
      f ((v ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) ⊗ₜ[k]
          PiTensorProduct.tprod k c) =
        g ((v ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) ⊗ₜ[k]
          PiTensorProduct.tprod k c)) : f = g := by
  apply TensorProduct.ext'
  intro x c
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul v x =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
          simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hx, hy]
      | tmul a b =>
          induction a using PiTensorProduct.induction_on with
          | add x y hx hy =>
              simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx, hy]
          | smul_tprod s a =>
              induction b using PiTensorProduct.induction_on with
              | add x y hx hy =>
                  simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hx, hy]
              | smul_tprod t b =>
                  induction c using PiTensorProduct.induction_on with
                  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
                  | smul_tprod q c =>
                      simpa only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul,
                        smul_smul, mul_comm, mul_left_comm, mul_assoc]
                        using congrArg (fun y : E => s • (t • (q • y))) (h v a b c)

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- The literal original prefix, ideal block and suffix word in its original order. -/
def surroundedIdealWord (left right m : ℕ) (a : Fin left → A) (b : Fin m → I.Algebra)
    (c : Fin right → A) : Fin (left + right + m) → A := fun i =>
  if hleft : i.val < left then a ⟨i.val, hleft⟩
  else if hmiddle : i.val < left + m then I.subtypeHom (b ⟨i.val - left, by omega⟩)
  else c ⟨i.val - (left + m), by omega⟩

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem surroundedIdealWord_leading (left right m : ℕ)
    (a : Fin left → A) (b : Fin m → I.Algebra) (c : Fin right → A) (i : Fin left) :
    surroundedIdealWord k A I left right m a b c ⟨i.val, by omega⟩ = a i := by
  simp only [surroundedIdealWord, dite_eq_left i.isLt]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem surroundedIdealWord_middle (left right m : ℕ)
    (a : Fin left → A) (b : Fin m → I.Algebra) (c : Fin right → A) (i : Fin m) :
    surroundedIdealWord k A I left right m a b c ⟨left + i.val, by omega⟩ =
      I.subtypeHom (b i) := by
  have hleft : ¬ left + i.val < left := by omega
  have hmiddle : left + i.val < left + m := by omega
  simp only [surroundedIdealWord, dite_eq_right hleft, dite_eq_left hmiddle,
    Nat.add_sub_cancel_left]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem surroundedIdealWord_trailing (left right m : ℕ)
    (a : Fin left → A) (b : Fin m → I.Algebra) (c : Fin right → A) (i : Fin right) :
    surroundedIdealWord k A I left right m a b c ⟨left + m + i.val, by omega⟩ = c i := by
  have hleft : ¬ left + m + i.val < left := by omega
  have hmiddle : ¬ left + m + i.val < left + m := by omega
  simp only [surroundedIdealWord, dite_eq_right hleft, dite_eq_right hmiddle,
    Nat.add_sub_cancel_left]

/-- The original internal pair lies at the prefix length plus its internal position. -/
def surroundedIdealFaceIndex (left right n : ℕ) (i : Fin (n + 1)) :
    Fin (left + right + n + 1) := ⟨left + i.val, by omega⟩

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Multiplication in the ideal block agrees with multiplication at its original ambient position. -/
theorem surroundedIdealWord_mulAdjacent (left right n : ℕ)
    (a : Fin left → A) (b : Fin (n + 2) → I.Algebra) (c : Fin right → A)
    (i : Fin (n + 1)) :
    hochschildMulAdjacent (surroundedIdealFaceIndex left right n i)
        (surroundedIdealWord k A I left right (n + 2) a b c) =
      surroundedIdealWord k A I left right (n + 1) a (hochschildMulAdjacent i b) c := by
  funext t
  let p := surroundedIdealFaceIndex left right n i
  by_cases htp : t = p
  · subst t
    rw [hochschildMulAdjacent, ite_eq_left rfl]
    have hfirst : p.castSucc = (⟨left + i.castSucc.val, by omega⟩ :
        Fin (left + right + (n + 2))) := by
      apply Fin.ext
      rfl
    have hsecond : p.succ = (⟨left + i.succ.val, by omega⟩ :
        Fin (left + right + (n + 2))) := by
      apply Fin.ext
      dsimp [p, surroundedIdealFaceIndex]
      omega
    rw [hfirst, hsecond, surroundedIdealWord_middle, surroundedIdealWord_middle]
    change I.subtypeHom (b i.castSucc) * I.subtypeHom (b i.succ) =
      surroundedIdealWord k A I left right (n + 1) a (hochschildMulAdjacent i b) c
        ⟨left + i.val, by omega⟩
    rw [surroundedIdealWord_middle, hochschildMulAdjacent, ite_eq_left rfl]
    exact (map_mul I.subtypeHom _ _).symm
  · rw [hochschildMulAdjacent, ite_eq_right htp]
    by_cases hleft : t.val < left
    · let l : Fin left := ⟨t.val, hleft⟩
      have hle : t ≤ p := by
        change t.val ≤ left + i.val
        omega
      rw [Fin.succAbove_succ_of_le p t hle]
      have hsource : t.castSucc = (⟨l.val, by omega⟩ :
          Fin (left + right + (n + 2))) := by
        apply Fin.ext
        rfl
      have htarget : t = (⟨l.val, by omega⟩ : Fin (left + right + (n + 1))) := by
        apply Fin.ext
        rfl
      rw [hsource, surroundedIdealWord_leading, htarget, surroundedIdealWord_leading]
    · by_cases hmiddle : t.val < left + (n + 1)
      · let j : Fin (n + 1) := ⟨t.val - left, by omega⟩
        have htarget : t = (⟨left + j.val, by omega⟩ : Fin (left + right + (n + 1))) := by
          apply Fin.ext
          dsimp [j]
          omega
        have hjne : j ≠ i := by
          intro hji
          apply htp
          apply Fin.ext
          have hvalue := congrArg Fin.val hji
          dsimp [j, p, surroundedIdealFaceIndex] at hvalue ⊢
          omega
        by_cases hji : j ≤ i
        · have hle : t ≤ p := by
            change t.val ≤ left + i.val
            have hvalue : j.val ≤ i.val := hji
            dsimp [j] at hvalue
            omega
          rw [Fin.succAbove_succ_of_le p t hle]
          have hsource : t.castSucc = (⟨left + j.castSucc.val, by omega⟩ :
              Fin (left + right + (n + 2))) := by
            apply Fin.ext
            dsimp [j]
            omega
          rw [hsource, surroundedIdealWord_middle, htarget, surroundedIdealWord_middle,
            hochschildMulAdjacent, ite_eq_right hjne, Fin.succAbove_succ_of_le i j hji]
        · have hij : i < j := lt_of_not_ge hji
          have hlt : p < t := by
            change left + i.val < t.val
            have hvalue : i.val < j.val := hij
            dsimp [j] at hvalue
            omega
          rw [Fin.succAbove_succ_of_lt p t hlt]
          have hsource : t.succ = (⟨left + j.succ.val, by omega⟩ :
              Fin (left + right + (n + 2))) := by
            apply Fin.ext
            dsimp [j]
            omega
          rw [hsource, surroundedIdealWord_middle, htarget, surroundedIdealWord_middle,
            hochschildMulAdjacent, ite_eq_right hjne, Fin.succAbove_succ_of_lt i j hij]
      · let l : Fin right := ⟨t.val - (left + (n + 1)), by omega⟩
        have hlt : p < t := by
          change left + i.val < t.val
          omega
        rw [Fin.succAbove_succ_of_lt p t hlt]
        have hsource : t.succ = (⟨left + (n + 2) + l.val, by omega⟩ :
            Fin (left + right + (n + 2))) := by
          apply Fin.ext
          dsimp [l]
          omega
        have htarget : t = (⟨left + (n + 1) + l.val, by omega⟩ :
            Fin (left + right + (n + 1))) := by
          apply Fin.ext
          dsimp [l]
          omega
        rw [hsource, surroundedIdealWord_trailing, htarget, surroundedIdealWord_trailing]

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- The coordinate tensor retains V, the original ambient contexts and the original positive ideal block. -/
abbrev surroundedIdealCoordinate (left right n : ℕ) :=
  (V ⊗[k] (TensorPower k left A ⊗[k] TensorPower k right A)) ⊗[k]
    TensorPower k (n + 1) I.Algebra

/-- Native tensor associators put the selected ideal block between its original prefix and suffix. -/
def surroundedIdealTensorRearrangement (left right n : ℕ) :
    surroundedIdealCoordinate k A I V left right n ≃ₗ[k]
      V ⊗[k] ((TensorPower k left A ⊗[k] TensorPower k (n + 1) I.Algebra) ⊗[k]
        TensorPower k right A) :=
  (TensorProduct.assoc k V (TensorPower k left A ⊗[k] TensorPower k right A)
      (TensorPower k (n + 1) I.Algebra)).trans
    (TensorProduct.congr (LinearEquiv.refl k V)
      ((TensorProduct.assoc k (TensorPower k left A) (TensorPower k right A)
          (TensorPower k (n + 1) I.Algebra)).trans
        ((TensorProduct.congr (LinearEquiv.refl k (TensorPower k left A))
            (TensorProduct.comm k (TensorPower k right A)
              (TensorPower k (n + 1) I.Algebra))).trans
          (TensorProduct.assoc k (TensorPower k left A)
            (TensorPower k (n + 1) I.Algebra) (TensorPower k right A)).symm)))

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Every original factor keeps its value when the selected block is placed in its source order. -/
theorem surroundedIdealTensorRearrangement_tprod (left right n : ℕ) (v : V)
    (a : Fin left → A) (b : Fin (n + 1) → I.Algebra) (c : Fin right → A) :
    surroundedIdealTensorRearrangement k A I V left right n
        ((v ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k c)) ⊗ₜ[k]
          PiTensorProduct.tprod k b) =
      v ⊗ₜ[k] ((PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) ⊗ₜ[k]
        PiTensorProduct.tprod k c) := by
  simp only [surroundedIdealTensorRearrangement, LinearEquiv.trans_apply,
    TensorProduct.assoc_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.comm_tmul, TensorProduct.assoc_symm_tmul]

/-- Original ideal inclusion and native tensor concatenation construct the ambient word map. -/
def surroundedIdealTensorToAmbient (left right n : ℕ) :
    surroundedIdealCoordinate k A I V left right n →ₗ[k]
      V ⊗[k] TensorPower k (left + right + n + 1) A :=
  let block : TensorPower k (n + 1) I.Algebra →ₗ[k] TensorPower k (n + 1) A :=
    PiTensorProduct.map (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))
  let prefixMap : TensorPower k left A ⊗[k] TensorPower k (n + 1) I.Algebra →ₗ[k]
      TensorPower k (left + (n + 1)) A :=
    (TensorPower.mulEquiv : TensorPower k left A ⊗[k] TensorPower k (n + 1) A ≃ₗ[k]
      TensorPower k (left + (n + 1)) A).toLinearMap.comp (TensorProduct.map LinearMap.id block)
  let word : (TensorPower k left A ⊗[k] TensorPower k (n + 1) I.Algebra) ⊗[k]
      TensorPower k right A →ₗ[k] TensorPower k (left + right + n + 1) A :=
    (TensorPower.cast k A (by omega : left + (n + 1) + right = left + right + n + 1)).toLinearMap.comp
      ((TensorPower.mulEquiv : TensorPower k (left + (n + 1)) A ⊗[k]
        TensorPower k right A ≃ₗ[k] TensorPower k (left + (n + 1) + right) A).toLinearMap.comp
          (TensorProduct.map prefixMap LinearMap.id))
  (TensorProduct.map (LinearMap.id : V →ₗ[k] V) word).comp
    (surroundedIdealTensorRearrangement k A I V left right n).toLinearMap

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- The constructed native map keeps exactly the original ordered ambient word. -/
theorem surroundedIdealTensorToAmbient_tprod (left right n : ℕ) (v : V)
    (a : Fin left → A) (b : Fin (n + 1) → I.Algebra) (c : Fin right → A) :
    surroundedIdealTensorToAmbient k A I V left right n
        ((v ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k c)) ⊗ₜ[k]
          PiTensorProduct.tprod k b) =
      v ⊗ₜ[k] PiTensorProduct.tprod k
        (surroundedIdealWord k A I left right (n + 1) a b c) := by
  let hlen : left + (n + 1) + right = left + right + n + 1 := by omega
  let block : TensorPower k (n + 1) I.Algebra →ₗ[k] TensorPower k (n + 1) A :=
    PiTensorProduct.map (fun _ : Fin (n + 1) => (I.subtypeHom : I.Algebra →ₗ[k] A))
  let prefixMap : TensorPower k left A ⊗[k] TensorPower k (n + 1) I.Algebra →ₗ[k]
      TensorPower k (left + (n + 1)) A :=
    (TensorPower.mulEquiv : TensorPower k left A ⊗[k] TensorPower k (n + 1) A ≃ₗ[k]
      TensorPower k (left + (n + 1)) A).toLinearMap.comp (TensorProduct.map LinearMap.id block)
  let word : (TensorPower k left A ⊗[k] TensorPower k (n + 1) I.Algebra) ⊗[k]
      TensorPower k right A →ₗ[k] TensorPower k (left + right + n + 1) A :=
    (TensorPower.cast k A hlen).toLinearMap.comp
      ((TensorPower.mulEquiv : TensorPower k (left + (n + 1)) A ⊗[k]
        TensorPower k right A ≃ₗ[k] TensorPower k (left + (n + 1) + right) A).toLinearMap.comp
          (TensorProduct.map prefixMap LinearMap.id))
  change TensorProduct.map (LinearMap.id : V →ₗ[k] V) word
      (surroundedIdealTensorRearrangement k A I V left right n
        ((v ⊗ₜ[k] (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k c)) ⊗ₜ[k]
          PiTensorProduct.tprod k b)) = _
  rw [surroundedIdealTensorRearrangement_tprod, TensorProduct.map_tmul, LinearMap.id_apply]
  apply congrArg (fun x : TensorPower k (left + right + n + 1) A => v ⊗ₜ[k] x)
  change TensorPower.cast k A hlen
      ((TensorPower.mulEquiv : TensorPower k (left + (n + 1)) A ⊗[k]
        TensorPower k right A ≃ₗ[k] TensorPower k (left + (n + 1) + right) A)
        (TensorProduct.map prefixMap LinearMap.id
          ((PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b) ⊗ₜ[k]
            PiTensorProduct.tprod k c))) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  change TensorPower.cast k A hlen
      ((TensorPower.mulEquiv : TensorPower k (left + (n + 1)) A ⊗[k]
        TensorPower k right A ≃ₗ[k] TensorPower k (left + (n + 1) + right) A)
        ((TensorPower.mulEquiv : TensorPower k left A ⊗[k] TensorPower k (n + 1) A ≃ₗ[k]
          TensorPower k (left + (n + 1)) A)
            (TensorProduct.map LinearMap.id block
              (PiTensorProduct.tprod k a ⊗ₜ[k] PiTensorProduct.tprod k b)) ⊗ₜ[k]
          PiTensorProduct.tprod k c)) = _
  rw [TensorProduct.map_tmul, LinearMap.id_apply]
  dsimp only [block]
  rw [PiTensorProduct.map_tprod, originalTensorPowerMul_tprod,
    originalTensorPowerMul_tprod, TensorPower.cast_tprod]
  apply congrArg (PiTensorProduct.tprod k)
  funext i
  by_cases hleft : i.val < left
  · let l : Fin left := ⟨i.val, hleft⟩
    have hi : Fin.cast (by omega : left + right + n + 1 = left + (n + 1) + right) i =
        (l.castAdd (n + 1)).castAdd right := by
      apply Fin.ext
      rfl
    change Fin.append (Fin.append a (fun j => I.subtypeHom (b j))) c
        (Fin.cast (by omega) i) = surroundedIdealWord k A I left right (n + 1) a b c i
    rw [hi, Fin.append_left, Fin.append_left]
    simp only [surroundedIdealWord, dite_eq_left hleft]
    rfl
  · by_cases hmiddle : i.val < left + (n + 1)
    · let j : Fin (n + 1) := ⟨i.val - left, by omega⟩
      have hi : Fin.cast (by omega : left + right + n + 1 = left + (n + 1) + right) i =
          (Fin.natAdd left j).castAdd right := by
        apply Fin.ext
        dsimp [j]
        omega
      change Fin.append (Fin.append a (fun j => I.subtypeHom (b j))) c
          (Fin.cast (by omega) i) = surroundedIdealWord k A I left right (n + 1) a b c i
      rw [hi, Fin.append_left, Fin.append_right]
      simp only [surroundedIdealWord, dite_eq_right hleft, dite_eq_left hmiddle]
      rfl
    · let l : Fin right := ⟨i.val - (left + (n + 1)), by omega⟩
      have hi : Fin.cast (by omega : left + right + n + 1 = left + (n + 1) + right) i =
          Fin.natAdd (left + (n + 1)) l := by
        apply Fin.ext
        dsimp [l]
        omega
      change Fin.append (Fin.append a (fun j => I.subtypeHom (b j))) c
          (Fin.cast (by omega) i) = surroundedIdealWord k A I left right (n + 1) a b c i
      rw [hi, Fin.append_right]
      simp only [surroundedIdealWord, dite_eq_right hleft, dite_eq_right hmiddle]
      rfl

/-- The selected original ideal face uses the regular ideal-word face. -/
def surroundedIdealTensorFace (left right n : ℕ) (i : Fin (n + 1)) :
    surroundedIdealCoordinate k A I V left right (n + 1) →ₗ[k]
      surroundedIdealCoordinate k A I V left right n :=
  TensorProduct.map LinearMap.id (regularWordFace k I.Algebra n i.castSucc)

/-- The original ambient word face at the original internal pair, with V unchanged. -/
def surroundedCoefficientWordFace (left right n : ℕ) (i : Fin (n + 1)) :
    V ⊗[k] TensorPower k (left + right + n + 2) A →ₗ[k]
      V ⊗[k] TensorPower k (left + right + n + 1) A :=
  TensorProduct.map LinearMap.id
    (regularWordFace k A (left + right + n) (surroundedIdealFaceIndex left right n i).castSucc)

omit [I.IsTwoSided] in
/-- The original internal face commutes with the native ordered tensor rearrangement. -/
theorem surroundedIdealTensorToAmbient_face (left right n : ℕ) (i : Fin (n + 1)) :
    (surroundedCoefficientWordFace k A V left right n i).comp
        (surroundedIdealTensorToAmbient k A I V left right (n + 1)) =
      (surroundedIdealTensorToAmbient k A I V left right n).comp
        (surroundedIdealTensorFace k A I V left right n i) := by
  apply originalContextTensor_ext k A I.Algebra V
  intro v a c b
  simp only [LinearMap.comp_apply, surroundedIdealTensorToAmbient_tprod,
    surroundedCoefficientWordFace, surroundedIdealTensorFace, TensorProduct.map_tmul,
    LinearMap.id_apply, regularWordFace_castSucc_tprod]
  rw [surroundedIdealWord_mulAdjacent]

end ModuleCat.Algebra.Hochschild.NonUnital
