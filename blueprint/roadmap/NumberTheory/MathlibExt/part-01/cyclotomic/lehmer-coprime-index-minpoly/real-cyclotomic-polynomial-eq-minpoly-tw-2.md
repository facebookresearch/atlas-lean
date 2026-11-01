---
article_id: af_df21cbfa18264b53c7ea23b1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.realCyclotomicPolynomial_eq_minpoly_two_cos_of_coprime
---

# Real Cyclotomic Polynomial eq minpoly two cos of coprime

Minimal polynomial of `2 cos (2πk/n)` for `1 ≤ k ≤ n` with `Nat.Coprime k n`:
it equals the real cyclotomic polynomial at `n` (for `2 < n`). The range hypotheses are unused;
see `realCyclotomicPolynomial_eq_minpoly_two_cos`.

## Depends on

- [Real Cyclotomic Polynomial](../real-cyclotomic-polynomial.md)

## Proof depends on

- [Real Cyclotomic Polynomial eq minpoly two cos](real-cyclotomic-polynomial-eq-minpoly-tw.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Cyclotomic.LehmerCoprimeIndexMinpoly](../../../../../../sources/v2/MathlibExt.md)
- Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19 (2016), source lines 83-90: https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455 normalized no-final-newline span SHA-256 e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039
