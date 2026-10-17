---
article_id: af_dbb2b20b1430cd99c3c81546
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.medianGenocchiOdd_divisibility
---

# Median Genocchi Divisibility

For `n ≥ 1`, `H_(2n+3)` is divisible by `2^n`, and the quotient is
congruent modulo `6` to `1` for odd `n` and to `4` for even `n`.

This records the divisibility theorem from Kwang-Wu Chen, *An Interesting Lemma
for Regular C-fractions*, Journal of Integer Sequences 6 (2003), Article 03.4.8:
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.tex>.

Proof: The antisymmetry of the Euler-Seidel matrix of the Genocchi numbers writes
`H_(2n+3)` as an alternating sum of Legendre-Stirling numbers times `k! (k+1)!`.
Pulling a power of two out of each term gives the factor `2^n`; in the remaining
sum every term from the fourth on is divisible by 6, which gives the residue.
The divisibility and residue arguments are Chen's, applied to this finite sum
instead of his continued fraction.

## Depends on

- [Median Genocchi Odd](median-genocchi-number/median-genocchi-odd.md)

## Proof depends on

- [Euler Seidel Matrix](../part-02/euler-seidel-matrix/euler-seidel-matrix.md)
- [Euler Seidel Matrix eq sum](../part-02/euler-seidel-matrix/euler-seidel-matrix-eq-sum.md)
- [Genocchi Number](../../../../../NumberTheory/MathlibExt/part-06/genocchi-number/genocchi-number.md)
- [Genocchi Number Via Bernoulli](median-genocchi-number/genocchi-number-via-bernoulli.md)
- [Genocchi Number Via Bernoulli eq genocchi Number](../../../../../NumberTheory/MathlibExt/part-06/genocchi-bernoulli/genocchi-number-via-bernoulli-eq-genocch.md)
- [Genocchi Number eq](../../../../../NumberTheory/MathlibExt/part-06/genocchi-number/genocchi-number-eq.md)
- [Genocchi Power Series](../../../../../NumberTheory/MathlibExt/part-06/genocchi-number/genocchi-power-series.md)
- [Genocchi Power Series eq](../../../../../NumberTheory/MathlibExt/part-06/genocchi-number/genocchi-power-series-eq.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.MedianGenocchiDivisibility](../../../../../../sources/v2/MathlibExt.md)
