---
article_id: af_53752c956ce4243229446dc4
declaration: theorem
origin: cited
lean: RandomProjection.random_projection_concentration
---

# Lemma 9.4.24 (Random projection)

There exists a constant $C > 0$ so that the following holds. Let $m \geq d$ and let $P \colon \mathbb{R}^m \to \mathbb{R}^d$ denote the orthogonal projection onto the subspace spanned by the first $d$ coordinates. Let $z$ be a uniform random point on the unit sphere in $\mathbb{R}^m$. Let $y = Pz$ and $Y = |y|$. Then, for all $t \geq 0$, $\mathbb{P}(|Y - \sqrt{d/m}| \geq t) \leq 2e^{-cmt^2}$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Corollary 9.4.14 (Concentration of measure on the sphere)](143-concentration-of-measure-on-the-sphere.md)
- [Lemma 9.4.20 (Median vs. mean for subGaussian distributions)](147-median-vs-mean-for-subgaussian-distribut.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.4](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
