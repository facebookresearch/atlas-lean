---
article_id: af_5cfcdccb734005cb3b0a538c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZMod.carlitz_sum_inv_block_Ico_eq_zero_of_five_le
---

# Carlitz Block Harmonic

Block harmonic sum vanishing modulo `p ^ 2` for primes `p ≥ 5`.

Cited original: L. Carlitz, "A note on Wolstenholme's theorem", American
Mathematical Monthly 61 (1954), 174–176.

Here `k : ℕ` follows the source application; the sum runs over `r = 1, …, p - 1`
via `Finset.Ico 1 p`; under the hypotheses all denominators are units modulo
`p ^ 2`.
Proves `Wanted` entry `ZMod.carlitz_sum_inv_block_Ico_eq_zero_of_five_le`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.CarlitzBlockHarmonic](../../../../sources/v2/MathlibExt.md)
- Jerry Metzger and Thomas Richards, "A Prisoner Problem Variation", `https://cs.uwaterloo.ca/journals/JIS/VOL18/Metzger/metz1.tex`, lines 657–662 (live file SHA-256 `660bfcb06fb3e08814f30b24659410fba256effd4161ec1cca7ea9fc3d20b0ec`; exact source-span SHA-256 `0aa191b703844e65e7e2fd1c181532b3409c2720e7317d93f130d66c66f34d0f`; concept `jis_dep_8bfbdf778d8b84efc2cbaafc`).
