# The operator norm is submultiplicative

Let $X$, $Y$ and $Z$ be normed spaces over $\mathbb R$ or $\mathbb C$, and let $T:X\to Y$ and $S:Y\to Z$ be bounded linear operators, with operator norm $\lVert T\rVert=\sup_{\lVert x\rVert\le1}\lVert Tx\rVert$. Then $ST$ is bounded and

$$\lVert ST\rVert\le\lVert S\rVert\,\lVert T\rVert .$$

In particular $\lVert T^n\rVert\le\lVert T\rVert^n$ for a bounded operator $T$ on $X$ and $n\ge0$, and $\lVert AB\rVert\le\lVert A\rVert\,\lVert B\rVert$ for $d\times d$ matrices with the operator norm induced by any norm on $\mathbb R^d$.

## Expansion

A proof page must derive the bound from $\lVert STx\rVert\le\lVert S\rVert\,\lVert Tx\rVert\le\lVert S\rVert\,\lVert T\rVert\,\lVert x\rVert$ and the definition of the operator norm as a supremum, and the power bound by induction.

## Sources

- E. Kreyszig, *Introductory Functional Analysis with Applications*, Wiley, 1978, Chapter 2, Section 2.7.
