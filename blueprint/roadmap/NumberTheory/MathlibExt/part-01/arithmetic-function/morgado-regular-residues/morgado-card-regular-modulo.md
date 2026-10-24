---
article_id: af_b2bda5345b568ccffeb80c2c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.morgado_card_regular_modulo
---

# Morgado card regular modulo

Morgado's formula for the number of regular residues modulo `n`
(equation `eq:2`).

For each `n`, an integer `m` is regular modulo `n` when the congruence
`m ^ 2 * x = m` has a solution; `ϱ(n)` counts the residue classes with this
property (OEIS `A055653`). A divisor `d ∣ n` is unitary iff
`Nat.Coprime d (n / d)`; the sum is `∑ d udiv n, Nat.totient d`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ncard regular eq sum totient unitary Divisors](ncard-regular-eq-sum-totient-unitary-div.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.MorgadoRegularResidues](../../../../../../sources/v2/MathlibExt.md)
- Klaus Dohmen and Mandy Lange-Geisler, "On the Number of Regular Integers Modulo n and Its Significance for Cryptography", Journal of Integer Sequences 29 (2026), Article 26.2.4, Definition [Morgado 1972] lines 108-112 and Theorem [Morgado 1972] (equation `eq:2`) lines 127-132: https://cs.uwaterloo.ca/journals/JIS/VOL29/Dohmen/dohmen4.tex The formula is attributed to J. Morgado (1972). It follows from `ncard_regular_eq_sum_totient_unitaryDivisors`; the filter spells out `n.unitaryDivisors` and keeps the source's shape. Proves `Wanted` entry `morgado_card_regular_modulo`.
