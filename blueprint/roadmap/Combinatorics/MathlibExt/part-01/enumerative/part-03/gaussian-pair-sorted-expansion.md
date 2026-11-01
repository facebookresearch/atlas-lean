---
article_id: af_cb5500b5760d6fcdd3c0ba0f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.gaussian_pair_sorted_expansion
---

# Gaussian QBinomial

The `q-(1+q)`-analogue of the Gaussian coefficient: the `q`-binomial
equals the sum over pair-sorted words of `q^inv * (1 + q)^ascOdd`.

The left side renders the Gaussian `q`-binomial by the source's
MacMahon inversion generating polynomial over all words (lines
128–147), since Mathlib has no canonical `q`-binomial identifier;
the pair-sorted set is the source's Definition 1 (lines 224–236)
and `ascOdd` its odd-ascent statistic (lines 291–298).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GaussianQBinomial](../../../../../../sources/v2/MathlibExt.md)
- Richard Ehrenborg and Margaret A. Readdy, "The Gaussian Coefficient Revisited," Journal of Integer Sequences 19 (2016), Article 16.7.8, Corollary 3 (label corollary_q_1_q), equation (equation_smaller_q_binomial), lines 301–311, https://cs.uwaterloo.ca/journals/JIS/VOL19/Ehrenborg/ehr3.tex
