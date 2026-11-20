---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.boundaryPowerGeometry
---

# Boundary-power geometry for three consecutive runs

Prove one bundled theorem for the actual transcribed `powerloop`. Let
`s a b c n : Nat` satisfy `0 < a`, `0 < b`, `0 < c`,
`s + a + b + c ≤ n`, and `n ≤ PY_LIST_MAX`; these describe three
consecutive runs `A`, `B`, and `C`, beginning at zero-based offset `s`, inside
the same list. Write

```text
P(x, u, v) =
  powerloop (BitVec.ofNat 64 x) (BitVec.ofNat 64 u)
    (BitVec.ofNat 64 v) (BitVec.ofNat 64 n),
pAB = P(s, a, b),
pBC = P(s + a, b, c).
```

The single theorem concludes all three laws:

- **Adjacent powers differ:** `pAB ≠ pBC`.
- **Right absorption:** if `pAB < pBC`, then
  `P(s, a, b + c) = pAB`.
- **Left absorption:** if `pBC < pAB`, then
  `P(s, a + b, c) = pBC`.

Here `P` is only local notation for the transcribed finite-width function, not
a replacement mathematical specification. The proof must derive from the
displayed natural-number hypotheses that all four calls are valid
`ValidPowerloopInput`s. In particular, every `BitVec.ofNat 64` argument converts
back to the displayed natural number, is signed-nonnegative, and every position
or length sum used for `s + a`, `a + b`, and `b + c` is exact rather than
modulo `2^64`. The necessary signed and no-wrap inequalities come from
`s + a + b + c ≤ n ≤ PY_LIST_MAX`; they are not additional assumptions.

For the proof, transfer the four transcribed results to their canonical
quotient-bit characterizations. The doubled midpoints of `A`, `B`, and `C` are
strictly ordered. A single quotient bit at a fixed depth cannot make the shared
midpoint simultaneously the right endpoint's `1` bit for the left boundary
and the left endpoint's `0` bit for the right boundary, which gives
non-equality. If one boundary first differs at a shallower depth, every
midpoint strictly inside the deeper boundary's dyadic cell has the same bit
prefix at that depth; replacing the deeper side by the midpoint of the merged
run therefore leaves the shallower power unchanged. Use canonical quotient
bits throughout, avoiding any choice between dual binary expansions.

## Depends on

- [Finite-width implementation model](../transcription/word-model.md)
- [powerloop](../transcription/powerloop.md)

## Proof depends on

- [powerloop input arithmetic bounds](../bit-equivalence/powerloop-input-bounds.md)
- [powerloop terminating-result characterization](../bit-equivalence/powerloop-result.md)

## Sources

- [CPython quotient-bit explanation](../../sources/listsort.md#the-merge-pattern)
- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [Munro-Wild node power](../../sources/munro-wild-powersort-notes.md#node-power)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
