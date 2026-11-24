# Exists unitary Group of kraus eq padded

Arbitrary unequal-family Kraus unitary equivalence after zero-padding to `r ⊕ s`.

Given `K : r → Matrix m n ℂ` and `L : s → Matrix m n ℂ` with `kraus K = kraus L`,
zero-pad both to the common index type `r ⊕ s`:

* source padded family places `K` on `Sum.inl` and zero on `Sum.inr`:
  `Sum.elim K (fun _ : s => 0)`;
* target padded family places zero on `Sum.inl` and `L` on `Sum.inr`:
  `Sum.elim (fun _ : r => 0) L`.

Then there exists a unitary `U : Matrix (r ⊕ s) (r ⊕ s) ℂ` in
`Matrix.unitaryGroup (r ⊕ s) ℂ` such that

`targetPad = mixKraus U sourcePad`,

i.e. for `j : r ⊕ s`, `targetPad j = ∑ i, U j i • sourcePad i` with no star
(`conj`) on the coefficient `U j i`. Conjugation appears only via `ᴴ` on
Kraus operators inside the CP sum, as in Watrous Theorem 2.12 / Corollary 2.23
without star.

No unpadded unitary on `r` or `s` is claimed for unequal cardinalities:
e.g. `[A]` and `[A/√2, A/√2]` have the same CP map but are not related by a
square unitary; they become unitarily related only after zero-padding to a
common type, here `r ⊕ s`. Empty `r`, `s`, and zero maps are supported
without `Nonempty` using `Fin 0` and empty sums.
