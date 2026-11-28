# Almost multilinear matroids

A matroid is almost multilinear when, for every $\varepsilon > 0$, a scaled rank function of a subspace arrangement approximates its rank function within $\varepsilon$.

A *polymatroid* $(E, \tilde r)$ is a finite set $E$ with a function $\tilde r \colon \mathcal{P}(E) \to \mathbb{R}_{\ge 0}$ that is monotone and submodular; it is *linear* over a [field](../../../Algebra/rings-and-fields/field.md) $F$ if $\tilde r(S) = \dim \sum_{e \in S} W_e$ for subspaces $W_e$ of a vector space over $F$. A finite [matroid](matroids-given-by-rank-functions.md) $M$ with ground set $E$ and rank function $r$ (in Mathlib, a `Matroid` with `Matroid.Finite`, and $r$ given by `Matroid.eRk`) is *almost multilinear* if for every $\varepsilon > 0$ there are a linear polymatroid $(E, \tilde r)$ and an integer $c \ge 1$ with

$$
\max_{S \subseteq E} \big| r(S) - \tilde r(S)/c \big| < \varepsilon .
$$

In the source's problem formulation the field $F$ is fixed together with the matroid, giving almost multilinearity over $F$.

## Depends on

- [Matroids](matroids-given-by-rank-functions.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Module over a semiring](../../../Algebra/modules/module.md)

## Proof depends on

None.

## Expansion

Every multilinear matroid is almost multilinear, taking the representing subspaces themselves for every $\varepsilon$.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Problem 1.3, Definition 2.4 and the definition of almost multilinear matroids that follows it, and the definition of polymatroids after Definition 2.1, of arXiv:2206.03465v3.
