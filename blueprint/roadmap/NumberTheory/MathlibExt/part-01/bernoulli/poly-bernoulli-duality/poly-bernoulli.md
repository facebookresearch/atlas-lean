---
article_id: af_b8fedd25e1b51330c75bcc6c
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.polyBernoulli
---

# Poly Bernoulli

Poly-Bernoulli number `Bₙ⁽ᵏ⁾` via Kaneko's explicit finite Stirling-number formula.

The source sums over `m = 1, …, n + 1` with denominator `(m : ℚ) ^ k`;
here this is reindexed by `r = m - 1` over `Finset.range (n + 1)`, so the
denominator is `(((r + 1 : ℕ) : ℚ) ^ k)`. The two sign factors
`(-1 : ℚ) ^ n` and `(-1 : ℚ) ^ r` are kept in this source-direct form.

Introduced by M. Kaneko, "Poly-Bernoulli numbers," Journal de Théorie des
Nombres de Bordeaux 9 (1997), 221–228; see also T. Arakawa and M. Kaneko,
"On poly-Bernoulli numbers," Commentarii Mathematici Universitatis
Sancti Pauli 48 (1999), 159–167, as cited by the source.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.PolyBernoulliDuality](../../../../../../sources/v2/MathlibExt.md)
- Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers," Journal of Integer Sequences 10 (2007), Article 07.4.1, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex>. The poly-Bernoulli generating-series definition and Kaneko's formula are lines 106–152 of the official TeX.
