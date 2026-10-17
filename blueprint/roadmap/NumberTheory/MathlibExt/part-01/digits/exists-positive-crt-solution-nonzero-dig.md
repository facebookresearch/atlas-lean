---
article_id: af_5520d2adbcddc03c52d234c7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.exists_positive_crt_solution_nonzero_digit_product_one
---

# Prodigious Crt Solution

Chinese-remainder-compatible positive integer with trivial nonzero-digit
product: any consistent system of congruences with `r_v = 0` whenever
`gcd(m_v, b) ≠ 1` is satisfied by some positive `c` with `p_b(c) = 1`.

`p_b(c)` is the product of the nonzero base-`b` digits of `c`; the
formalization requires `3 ≤ b` and a nonempty system, matching the
paper's `b > 2` setting.

## Depends on

- [Nonzero Digit Prod](../../part-10/prodigious-number/nonzero-digit-prod.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Digits.ProdigiousCrtSolution](../../../../../sources/v2/MathlibExt.md)
- Michael Gohn, Joshua Harrington, Sophia Lebiere, Hani Samamah, Kyla Shappell, and Tony W. H. Wong, "Arithmetic Progressions of b-Prodigious Numbers," Journal of Integer Sequences 25 (2022), Article 22.8.7, Lemma `lem:crt`, lines 178-180, <https://cs.uwaterloo.ca/journals/JIS/VOL25/Wong/wong42.tex>.
