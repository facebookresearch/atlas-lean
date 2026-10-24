---
article_id: af_173ead3f917bee14427ab45a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Nat.fermatNumber_mod_prime_exact_preperiod_period
---

# Fermat Residue Period

Exact preperiod and primitive period of Fermat-number residues modulo an odd prime.

This is the exact-preperiod/primitive-period expansion of Theorem `thm:5` in the section
"A simpler formulation of Aigner's theorem": for an odd prime `p` with
`orderOf (2 : ZMod p) = 2 ^ v * w` and `w` odd, writing `k := orderOf (2 : ZMod w)`, the
shifted residue sequence `n ↦ (Nat.fermatNumber (v + n) : ZMod p)` is periodic with period
`k`, no shift `h < v` admits any positive tail period, and every positive period of the
tail from `v` is divisible by `k`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.FermatResiduePeriod](../../../../sources/v2/MathlibExt.md)
- `https://cs.uwaterloo.ca/journals/JIS/VOL28/Klaska/klaska22.tex`, Theorem `thm:5`, lines 593--606 of `56ede62e8bb2abc2c9097317bce881d696be23082f48fa2822d297f0f11e65af.tex` (source SHA-256 `56ede62e8bb2abc2c9097317bce881d696be23082f48fa2822d297f0f11e65af`, excerpt SHA-256 `e4893c51946a5353f9ac51df8a431d7a4374170b122bfcb5befb12ae3d342bd7`). Concept `jis_dep_f3be3eca42e403215ccd3864` (grounded `jis_grounded_b5fc700e81e8282d5e992c5d`); accounting: 7 mentions / 3 papers / 2 proof uses. This is the complete selected theorem statement, not a prerequisite stage. Proves `Wanted` entry `fermatNumber_mod_prime_exact_preperiod_period`.
