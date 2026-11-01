---
article_id: af_b9ecf9c7bafe614a8ae4f45c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: FibonacciNormEquation.fibonacci_norm_eq_one_or_neg_one_iff
---

# Fibonacci Norm Equation

Integer solutions of `x ^ 2 - x * y - y ^ 2 = ±1` via integer-indexed
    Fibonacci numbers: `x ^ 2 - x * y - y ^ 2 = 1` or `= -1` iff there exist
    `n s : ℤ` with `s = 1` or `s = -1` such that `x = s * Int.fib n` and
    `y = s * Int.fib (n - 1)`.

Provenance (independently verified):
    - Bahar Demirtürk and Refik Keskin, “Integer Solutions of Some Diophantine
      Equations via Fibonacci and Lucas Numbers”, Journal of Integer Sequences
      12 (2009), Article 09.8.7.
    - Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL12/Demirturk/demirturk3.tex
    - Theorem 1.2 at source lines 171–175.
    - Full source SHA-256:
      964bc6bad9fc6d4c658004d156ce983da85ded092e640eb4a0749c96bec3de65
    - Normalized no-final-newline theorem-span SHA-256:
      651317db815f48ced07ee68335c24ed88a61934c1ef8ab23ffc3d90693892328
Proves `Wanted` entry `fibonacci_norm_eq_one_or_neg_one_iff`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.QuadraticForms.FibonacciNormEquation](../../../../../sources/v2/MathlibExt.md)
