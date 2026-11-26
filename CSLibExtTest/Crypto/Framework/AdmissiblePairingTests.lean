/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Framework.AdmissiblePairing

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
