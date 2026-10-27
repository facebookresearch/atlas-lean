---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.FractionalCascading.length_sample_le
---

# Length sample le

The sample length is at most half the catalog length, rounded up:
for an even length `2m` this is `m`, and for an odd length `2m + 1` it is
`m + 1`, matching `(xs.length + 1) / 2` exactly.

## Depends on

- [Sample](sample.md)

## Proof depends on

- [Two mul length sample le](two-mul-length-sample-le.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DataStructures.FractionalCascading](../../../../../../../../sources/v2/CSLibExt.md)
