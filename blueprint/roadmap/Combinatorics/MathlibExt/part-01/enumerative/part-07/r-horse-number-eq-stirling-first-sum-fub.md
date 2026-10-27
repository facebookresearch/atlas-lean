---
article_id: af_0c08b38e6d40bc4decb0ff5b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.rHorseNumber_eq_stirlingFirst_sum_fubini
---

# RHorse Number Fubini

For `r ≤ n`, the `r`-horse number — surjective maps `Fin n → Fin k` with
the first `r` values strictly increasing, summed over `k` — equals the signed
first-kind Stirling transform of the Fubini numbers, divided by `r!`.

Proof: Following Schreyer's proof of Theorem `thm:fubinir` (lines 216–240), the signed
falling-factorial expansion is evaluated at integers and transported to surjection counts by
image decomposition and binomial inversion, rather than by shift operators.

## Depends on

- [Fubini Number](../part-03/fubini-number/fubini-number.md)

## Proof depends on

- [Fubini Number eq sum](../part-03/fubini-number/fubini-number-eq-sum.md)
- [Signed Stirling First](../part-08/signed-stirling-first.md)
- [Sum signed Stirling First mul stirling Second](../part-08/stirling-matrices/sum-signed-stirling-first-mul-stirling-s.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.RHorseNumberFubini](../../../../../../sources/v2/MathlibExt.md)
- Benjamin Schreyer, "Rigged Horse Numbers and their Modular Periodicity," Journal of Integer Sequences 28 (2025), Article 25.4.1, Theorem (label thm:fubinir), lines 211–215, https://cs.uwaterloo.ca/journals/JIS/VOL28/Schreyer/schreyer7.tex
