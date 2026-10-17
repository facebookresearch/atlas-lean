---
article_id: af_0171ccffdf1c20d06d712628
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.binomial_fibonacci_convolution
---

# Binomial fibonacci convolution

Binomial convolution of Fibonacci numbers: the `n`-th alternating
binomial transform of `i ↦ fib (2n - i + k)` recovers `fib k`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Choose succ int](choose-succ-int.md)
- [Fib conv step](fib-conv-step.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.BinomialFibonacciConvolution](../../../../../sources/v2/MathlibExt.md)
- Brian Hopkins and Aram Tangboonduangjit, "Scaled Fibonacci- and Lucas-Producing Rational Polynomials," Journal of Integer Sequences 25 (2022), Article 22.3.5 (Corollary generalizing Corollary cor51(a), lines 989–1000), <https://cs.uwaterloo.ca/journals/JIS/VOL25/Hopkins/tang25.tex>. The sum is the `n`-th forward difference, which telescopes by Pascal's rule and `fib (m + 2) = fib m + fib (m + 1)`. Proves `Wanted` entry `binomial_fibonacci_convolution`.
