---
article_id: af_28b56fc730316431af7a2483
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fulton_morris_pisano_fixed_point
---

# Fulton Morris Pisano Fixed Point

Fulton–Morris fixed-point characterization of Pisano periods equal to the modulus.

Controlling source: Amirali Fatehizadeh and Daniel Yaqubi, "Average of the Fibonacci
Numbers," Journal of Integer Sequences 25 (2022), Article 22.2.6, live TeX at
`https://cs.uwaterloo.ca/journals/JIS/VOL25/Yaqubi/yaq6.tex`, file SHA-256
`460e70d342c78a6138fb5662d3463e293a93f52e776e0bef4489d30066b10f79`; exact
definition-and-theorem span lines 177–189, SHA-256
`f59a3e5fc68d0b7b406d75db1e7b38743d1a7392825ac9ec60242c199024da9a`. The theorem is
attributed there to John Fulton and William Morris, "On arithmetical functions related
to the Fibonacci numbers," Acta Arithmetica 16 (1969), 105–110,
DOI 10.4064/aa-16-2-105-110.

Least-return encoding: `hperiod` says the candidate `period` is positive, `hreturn`
says the pair `(Nat.fib t, Nat.fib (t + 1))` has returned to `(0, 1)` modulo `m` at
`t = period`, and `hleast` says no smaller positive `t` does so; jointly these state
that `period` is the least positive return (the Pisano period) of the Fibonacci pair
modulo `m`. The hypothesis `hm : 1 < m` preserves the source condition `m > 1`, and
`lambda` is required positive via `0 < lambda`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Fibonacci Prime Divisibility](fib-prime-dvd-fib-of-legendre-sub.md)
- [Fibonacci Five Adic Valuation](../../../part-01/padics/lengyel-fibonacci-five-adic.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.FultonMorrisPisanoFixedPoint](../../../../../../sources/v2/MathlibExt.md)
