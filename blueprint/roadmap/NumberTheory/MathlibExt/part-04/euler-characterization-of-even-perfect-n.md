---
article_id: af_998f5d67531df447b0c261c4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.euler_characterization_of_even_perfect_numbers
---

# Even Perfect Numbers

Euler's characterization of even perfect numbers: every even perfect
number has the Euclid form `2 ^ (p - 1) * (2 ^ p - 1)` with `p` and
`2 ^ p - 1` both prime.

The paper re-proves Euler's theorem to set up its generalization to
`α`-perfect numbers. The natural subtraction is safe since `p` prime
gives `p ≥ 2`. The known even perfects below `10^5`
(`6, 28, 496, 8128`) all match this form.
Proves `Wanted` entry `euler_characterization_of_even_perfect_numbers`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.EvenPerfectNumbers](../../../../sources/v2/MathlibExt.md)
- Paulo J. Almeida and Gabriel Cardoso, "An Extension of the Euclid-Euler Theorem to Certain α-Perfect Numbers," Journal of Integer Sequences 25 (2022), Article 22.8.4, Theorem [Euler] (unlabeled), lines 164–166, https://cs.uwaterloo.ca/journals/JIS/VOL25/Almeida/almeida9.tex
