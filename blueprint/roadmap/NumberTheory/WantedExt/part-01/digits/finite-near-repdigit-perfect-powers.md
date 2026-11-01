---
article_id: af_f1736ff731ab87bc2e12d2a6
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.finite_near_repdigit_perfect_powers
---

# Near Repdigit Perfect Powers Wanted

For fixed `l ≥ 3`, there are only finitely many perfect `l`-th powers all of
whose decimal digits are equal but one, except for the trivial families
`10 ^ (l * n)` and, for `l = 3`, `8 * 10 ^ (3 * n)`.

The digit condition says some digit `c < 10` occurs in `Nat.digits 10 y`
with exactly one digit different from `c`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Digits.NearRepdigitPerfectPowersWanted](../../../../../sources/v2/WantedExt.md)
- Omar Kihel and Florian Luca, "Perfect Powers with All Equal Digits but One," Journal of Integer Sequences 8 (2005), Article 05.5.7, Theorem 1 (label thm:1), lines 134–140, https://cs.uwaterloo.ca/journals/JIS/VOL8/Kihel/kihel7.tex.
