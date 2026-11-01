---
article_id: af_c125b564cb3920fca9449605
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.lehmer_cyclotomic_identity
---

# Lehmer cyclotomic identity

Denominator-cleared Laurent-polynomial form of `ψₙ(x + x⁻¹) = x^(-φ(n)/2) Φₙ(x)`:
multiplying the evaluation of the real cyclotomic polynomial at `x + x⁻¹` by
`x ^ (φ(n) / 2)` recovers the cyclotomic polynomial as a Laurent polynomial.

## Depends on

- [Real Cyclotomic Polynomial](../real-cyclotomic-polynomial.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Cyclotomic.LehmerLaurentIdentity](../../../../../../sources/v2/MathlibExt.md)
- Pinthira Tangsupphathawat and Vichian Laohakosol, "Minimal Polynomials of Algebraic Cosine Values at Rational Multiples of π", Journal of Integer Sequences 19 (2016), source lines 83-90: https://cs.uwaterloo.ca/journals/JIS/VOL19/Laohakosol/lao2.tex source SHA-256 15e6923301658b132cd14eb587f480152fbf9dd9554ecbc6ce321216d9314455 normalized no-final-newline span SHA-256 e91ccd0347f84043d402747f2c4aaf5e6d5f22cba3840369c7fb8a8732dbe039
