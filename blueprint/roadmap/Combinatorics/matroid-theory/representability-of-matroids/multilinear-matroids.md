# Multilinear matroids

A matroid multilinear over a field is one represented, for some integer $c \ge 1$, by subspaces whose spanned dimensions are $c$ times its ranks; $c = 1$ gives linear representations.

Let $F$ be a [field](../../../Algebra/rings-and-fields/field.md) and a finite [matroid](matroids-given-by-rank-functions.md) $M$ with ground set $E$ and rank function $r$ (in Mathlib, a `Matroid` with `Matroid.Finite`, and $r$ given by `Matroid.eRk`). $M$ is *multilinear over $F$* if there are an integer $c \ge 1$, a vector space $V$ over $F$ and subspaces $W_e \subseteq V$, $e \in E$, such that

$$
r(S) = \frac{1}{c} \dim \Big( \sum_{e \in S} W_e \Big) \qquad \text{for all } S \subseteq E;
$$

$M$ is *multilinear* if it is multilinear over some field. In the formulation of Kühne and Yashfe's undecidability theorem for multilinear matroids, a *$c$-arrangement* is a family of subspaces each of dimension exactly $c$ such that every sum of them has dimension a multiple of $c$, and $M$ is *representable as a $c$-arrangement* over $F$ if some such family satisfies the displayed identity. For a matroid without loops the two notions agree, since $r(\{e\}) = 1$ forces $\dim W_e = c$; a matroid with a loop $e$ can be multilinear (with $W_e = 0$) but is never representable as a $c$-arrangement.

## Depends on

- [Matroids](matroids-given-by-rank-functions.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Module over a semiring](../../../Algebra/modules/module.md)

## Proof depends on

None.

## Expansion

The case $c = 1$ is linear representability over $F$, so every matroid linear over $F$ is multilinear over $F$.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Definition 2.2 of arXiv:2206.03465v3.
- L. Kühne and G. Yashfe, "Representability of matroids by $c$-arrangements is undecidable", *Israel Journal of Mathematics* 252 (2022), no. 1, 95–147, doi:10.1007/s11856-022-2345-z; read as arXiv:1912.06123v2, <https://arxiv.org/abs/1912.06123v2>: Definition 1.1, Problem 1.2 and Definition 3.1 of arXiv:1912.06123v2.
