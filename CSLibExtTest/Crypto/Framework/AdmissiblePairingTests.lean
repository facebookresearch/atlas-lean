/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.EncodingConverters
import CSLibExt.Crypto.Framework.AdmissiblePairing
import MathlibExt.Computability.TuringMachine.Composition
import MathlibExt.Computability.TuringMachine.Program

/-! # Tests for admissible bilinear pairings -/

open Cslib.Crypto.Framework Cslib.Complexity MetaMathlibExt MetaMathlibExt.BitstringEncoding

-- The input framing agrees with the standard product encoding. A single actual polynomial-time
-- machine (the identity) works on these triples, including parameters of arbitrarily large size.
example : UniformlyPolyTime₂ (fun (i : List Bool) (x y : Bool) ↦ (i, x, y)) :=
  ⟨id, ⟨Turing.idComputableInPolyTime _⟩, fun _ _ _ ↦ rfl⟩

section

variable {ι : Type} [BitstringEncoding ι] {G H T : ι → Type}
  [∀ i, CommGroup (G i)] [∀ i, CommGroup (H i)] [∀ i, CommGroup (T i)]
  [∀ i, BitstringEncoding (G i)] [∀ i, BitstringEncoding (H i)] [∀ i, BitstringEncoding (T i)]
  {p : ι → ℕ}

-- The evaluator and its polynomial bound are selected before the public parameter.
example {e : (i : ι) → G i →* H i →* T i} (h : IsAdmissiblePairing p e) :
    ∃ run : List Bool → List Bool, ComplexityTheory.IsPolyTime run ∧
      ∀ i x y, run (delimit (bitEncode i) ++ bitEncode (x, y)) = bitEncode (e i x y) :=
  h.efficient

-- Multiplication of exponents takes place modulo the common order, not just in ℕ.
example {e : (i : ι) → G i →* H i →* T i} (h : IsAdmissiblePairing p e) (i : ι)
    (x : G i) (y : H i) (a b : ZMod (p i)) :
    e i (x ^ a.val) (y ^ b.val) = e i x y ^ (a * b).val := h.apply_pow_val i x y a b

-- A trivial pairing is excluded even if an efficient evaluator could be supplied.
example (i : ι) : ¬ IsAdmissiblePairing p (fun j ↦ (1 : G j →* H j →* T j)) := by
  intro h
  obtain ⟨x, y, hxy⟩ := h.nondegenerate i
  exact hxy rfl

-- Specialise to one source with the same representation; no coordinate isomorphism is needed.
example {e : (i : ι) → G i →* G i →* T i} (h : IsAdmissiblePairing p e) (i : ι)
    (g : G i) (hg : Subgroup.zpowers g = ⊤) : Subgroup.zpowers (e i g g) = ⊤ :=
  h.zpowers_pairing_eq_top i hg hg

example {e : (i : ι) → G i →* G i →* T i} (h : IsAdmissiblePairing p e) (i : ι)
    (x y : G i) : e i x y = e i y x := h.apply_comm i x y

end

section

variable {ι : Type} [BitstringEncoding ι] (B : ι → BilinearGroupData)
  [∀ i, BitstringEncoding (B i).G1] [∀ i, BitstringEncoding (B i).G2]
  [∀ i, BitstringEncoding (B i).GT]

-- The old two-source pairing is used unchanged, even with different source representations.
example (hp : ∀ i, (B i).q.Prime) (h : UniformlyPolyTime₂ (fun i ↦ (B i).e))
    (i : ι) (x : (B i).G1) (y : (B i).G2)
    (hx : Subgroup.zpowers x = ⊤) (hy : Subgroup.zpowers y = ⊤) :
    Subgroup.zpowers ((B i).e x y) = ⊤ :=
  (BilinearGroupData.isAdmissiblePairing B hp h).zpowers_pairing_eq_top i hx hy

-- The existing algebraic interface also allows composite orders; admissibility does not.
example (i : ι) (hi : (B i).q = 4) :
    ¬ IsAdmissiblePairing (fun j ↦ (B j).q) (fun j ↦ (B j).pairingHom) := by
  intro h
  have hp := h.prime i
  rw [hi] at hp
  exact (by decide : ¬ Nat.Prime 4) hp

end

namespace OrderTwoTest

open Turing TM2Program

-- The last four bits of a valid input are `true, x, false, y`, regardless of its parameter.
-- Keep the last three bits in a shift register; the result is its first bit AND its last bit.
private abbrev Window := Bool × Bool × Bool
private def shift (s : Window) (b : Bool) : Window := (s.2.1, s.2.2, b)
private def answer (s : Window) : List Bool := [s.1 && s.2.2]
private def zeroWindow : Window := (false, false, false)
private def evalWord (w : List Bool) := answer (w.foldl shift zeroWindow)

private def scanTM : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool × Window
  initialState := (false, zeroWindow)
  m _ := .pop () (fun s o ↦ match o with
      | some b => (true, shift s.2 b)
      | none => (false, s.2)) <|
    .branch Prod.fst (.goto fun _ ↦ ()) <|
    .push () (fun s ↦ s.2.1 && s.2.2.2) (.load (fun _ ↦ (false, zeroWindow)) .halt)

private theorem scan_run (w : List Bool) (s : Bool × Window) :
    Run scanTM.m (w.length + 1) ⟨some (), s, fun _ ↦ w⟩
      ⟨none, scanTM.initialState, fun _ ↦ answer (w.foldl shift s.2)⟩ := by
  induction w generalizing s with
  | nil =>
    apply Run.single
    apply congrArg (TM2.Cfg.mk none scanTM.initialState)
    funext k; cases k; rfl
  | cons b w ih =>
    apply Run.head _ (ih (true, shift s.2 b))
    apply congrArg some
    apply congrArg (TM2.Cfg.mk (some ()) (true, shift s.2 b))
    funext k; cases k; rfl

-- The machine code is finite and explicit; `noncomputable` is only for the polynomial bound.
private noncomputable def scanComputable : TM2ComputableInPolyTime id id evalWord where
  tm := scanTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun w := by
    refine ⟨⟨w.length + 1, ?_⟩, by simp⟩
    change Run scanTM.m _ (initList scanTM _) (haltList scanTM _)
    erw [List.map_id, List.map_id]
    have init : initList scanTM w = ⟨some (), (false, zeroWindow), fun _ ↦ w⟩ := by
      apply congrArg (TM2.Cfg.mk _ _); funext k; cases k; rfl
    have halt : haltList scanTM (evalWord w) = ⟨none, scanTM.initialState, fun _ ↦ evalWord w⟩ := by
      apply congrArg (TM2.Cfg.mk _ _); funext k; cases k; rfl
    rw [id_eq, id_eq, init, halt]
    exact scan_run w (false, zeroWindow)

private theorem evalWord_poly : ComplexityTheory.IsPolyTime evalWord := by
  obtain ⟨m⟩ := tm2ComputableInPolyTime_comp DenseSAT.DecodeBits.computable scanComputable
  exact tm2ComputableInPolyTime_comp (g := id) m DenseSAT.EncodeBits.computable

private abbrev C₂ := Multiplicative (ZMod 2)

private instance : BitstringEncoding C₂ where
  encode x := [decide (x.toAdd = 1)]
  decode
    | [false] => some (Multiplicative.ofAdd 0)
    | [true] => some (Multiplicative.ofAdd 1)
    | _ => none
  decode_encode := by decide

private abbrev B := BilinearGroupData.toyModel 2 (by decide)

private instance : BitstringEncoding B.G1 := (inferInstance : BitstringEncoding C₂)
private instance : BitstringEncoding B.G2 := (inferInstance : BitstringEncoding C₂)
private instance : BitstringEncoding B.GT := (inferInstance : BitstringEncoding C₂)

private theorem evalWord_spec (i : List Bool) (x y : C₂) :
    evalWord (delimit (bitEncode i) ++ bitEncode (x, y)) = bitEncode (B.e x y) := by
  change answer ((delimit (bitEncode i) ++
    [true, decide (x.toAdd = 1), false, decide (y.toAdd = 1)]).foldl shift zeroWindow) = _
  rw [List.foldl_append]
  change [decide (x.toAdd = 1) && decide (y.toAdd = 1)] = bitEncode (B.e x y)
  revert x y
  decide

-- In exponent order (0,0), (0,1), (1,0), (1,1), only the last pair gives the generator.
example : ([(0, 0), (0, 1), (1, 0), (1, 1)] : List (ZMod 2 × ZMod 2)).map
    (fun (a, b) ↦ evalWord (delimit (bitEncode ([] : List Bool)) ++
      bitEncode (Multiplicative.ofAdd a, Multiplicative.ofAdd b))) =
      [[false], [false], [false], [true]] := by decide

-- This is a nonempty family and the same evaluator accepts arbitrarily long public parameters.
example : IsAdmissiblePairing (fun _ : List Bool ↦ 2) (fun _ ↦ B.pairingHom) :=
  BilinearGroupData.isAdmissiblePairing (fun _ ↦ B) (fun _ ↦ by decide)
    ⟨evalWord, evalWord_poly, evalWord_spec⟩

end OrderTwoTest
