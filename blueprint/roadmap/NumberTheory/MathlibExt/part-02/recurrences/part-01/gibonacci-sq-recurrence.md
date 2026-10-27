---
article_id: af_ef2009ee4e7eb472538989ac
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.gibonacci_sq_recurrence
---

# Gibonacci Squares Recurrence

Squares of any Fibonacci-recurrence (Gibonacci) sequence satisfy the
third-order linear recurrence with coefficients `f_3 = 2`:
`g(n+3)^2 = 2*g(n+2)^2 + 2*g(n+1)^2 - g(n)^2`.

`Nat.fib 3 = 2` is the source's `f_3`. The recurrence's characteristic
polynomial `x^3 - 2x^2 - 2x + 1` has roots `α^2, β^2, -1` where `α, β`
are the Fibonacci roots. Verified computationally on 200 random integer
Gibonacci sequences at `n = 0..9`.
Proves `Wanted` entry `gibonacci_sq_recurrence`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.GibonacciSquaresRecurrence](../../../../../../sources/v2/MathlibExt.md)
- Thomas Koshy, "A Graph-Theoretic Model for a Generalized Fibonacci Gem," Journal of Integer Sequences 22 (2019), Article 19.4.1, Theorem 2 (label theorem02, equation equation02), lines 149–153, https://cs.uwaterloo.ca/journals/JIS/VOL22/Koshy/koshy7.tex
