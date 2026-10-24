---
article_id: af_d5f9be5353f3f1502f821463
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted.brun_twin_prime_reciprocal_series_summable
---

# Brun Twin Prime Reciprocals

The sum of reciprocals over twin-prime pairs, indexed by the smaller prime
`p` of each pair `(p, p + 2)`, converges over `ℝ`; a shared prime such as `5`
is intentionally counted once in each of `(3, 5)` and `(5, 7)`, and a finite
collection of twin-prime pairs is already covered because a finitely supported
function is summable.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Level Set](../../../part-10/selberg-sieve/level-set.md)
- [Level Sum](../../../part-10/selberg-sieve/level-sum.md)
- [Level Sum ge one](../../../part-10/selberg-sieve/level-sum-ge-one.md)
- [Level Weights](../../../part-10/selberg-sieve/level-weights.md)
- [Level Weights err Sum le](../../../part-10/selberg-sieve/level-weights-err-sum-le.md)
- [Level Weights main Sum](../../../part-10/selberg-sieve/level-weights-main-sum.md)
- [Level Weights one](../../../part-10/selberg-sieve/level-weights-one.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals](../../../../../../sources/v2/MathlibExt.md)
- Alexei Kourbatov and Marek Wolf, "On the First Occurrences of Gaps Between Primes in a Residue Class," Journal of Integer Sequences 23 (2020), `https://cs.uwaterloo.ca/journals/JIS/VOL23/Wolf/wolf2.tex`, lines 684–705; live and bundled source SHA-256 `f19705a8cece7b19aea01b0669774f24e42d49f9a262ff1c6ea0b4e6644e6d64` and exact cited span SHA-256 `dd71eb411be0ec74f9b3599bfdc17309c68109e03167163b629ab5949415e8da`. Corroboration: Prapanpong Pongsriiam and Kota Saito, "Palindromes and Antipalindromes in Short Intervals," Journal of Integer Sequences 26 (2023), `https://cs.uwaterloo.ca/journals/JIS/VOL26/Saito/saito1.tex`, lines 205–210; live and bundled source SHA-256 `0c721e5603affcd1b7a1dfeb67dcc79ef6a28132308cb081a1ee39c12515fabc` and exact cited span SHA-256 `b28ebf74254fb808313c73f910a0f7978dbae8e6987027c94e6924a6d81cc47f`. The sources attribute the theorem to V. Brun's 1919 paper on convergence or finiteness of the reciprocal twin-prime series.
