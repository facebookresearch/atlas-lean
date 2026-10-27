---
article_id: af_fc422364f191f04dc88c1004
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.infinitely_many_primes_fibonacci_pseudoprime
---

# Fibonacci Pseudoprime Infinitude

There are infinitely many primes `p` such that `F_{2p}` is a Fibonacci
pseudoprime.

A composite `n` is a Fibonacci pseudoprime when `n ∣ F_{n - (5/n)}` with
`D = 5`; compositeness is stated explicitly (`¬n.Prime ∧ 1 < n`).
Proves `Wanted` entry `infinitely_many_primes_fibonacci_pseudoprime`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.FibonacciPseudoprimeInfinitude](../../../../sources/v2/MathlibExt.md)
- Y. Hamahata and Y. Kokubun, "Cipolla Pseudoprimes," Journal of Integer Sequences 10 (2007), Article 07.8.6, Corollary 4 [Lehmer], lines 321–324 (Fibonacci-pseudoprime definition at lines 313–318), https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata2/hamahata44.tex
