# Matroids and their representations over division rings, by subspaces and by random variables

A finite matroid is given by a rank function on the subsets of its ground set; it can be represented by vectors over a division ring, by an arrangement of equidimensional subspaces, or by the joint entropies of random variables, and these notions give successively larger classes of matroids.

**Matroids.** A *matroid* $M = (E, r)$ consists of a finite ground set $E$ and a rank function $r \colon \mathcal{P}(E) \to \mathbb{Z}_{\ge 0}$ such that

1. $r(A) \le |A|$ for all $A \subseteq E$;
2. $r(A) \le r(B)$ whenever $A \subseteq B \subseteq E$;
3. $r(A \cup B) + r(A \cap B) \le r(A) + r(B)$ for all $A, B \subseteq E$.

A set $A$ is *independent* if $r(A) = |A|$. A pair $(E, r)$ with $r \colon \mathcal{P}(E) \to \mathbb{R}_{\ge 0}$ satisfying 2 and 3 is a *polymatroid*. A finite matroid is a finite object and can be given to an algorithm by the table of its rank function.

**Representations over division rings.** A *division ring* (skew field) $D$ is a ring with identity $1 \ne 0$ in which every nonzero element has a two-sided multiplicative inverse; a commutative division ring is a [field](../../../Algebra/rings-and-fields/field.md). A *representation of $M$ over $D$* is a map from $E$ to a right $D$-module such that a subset of $E$ is independent in $M$ exactly when its image is linearly independent over $D$. A matroid with a representation over some division ring is *skew-linear*; over a field this is the usual notion of a linear matroid.

**Multilinear representations.** Let $F$ be a field. A matroid $M = (E, r)$ is *multilinear over $F$* if there are an integer $c \ge 1$, a vector space $V$ over $F$ and subspaces $W_e \subseteq V$, $e \in E$, such that

$$
r(S) = \frac{1}{c} \dim \Big( \sum_{e \in S} W_e \Big) \qquad \text{for all } S \subseteq E;
$$

the family $(W_e)$ is then a *representation of $M$ as a $c$-arrangement*. The case $c = 1$ is linear representability over $F$.

**Entropic matroids.** A matroid $M = (E, r)$ is *entropic* if there are discrete random variables $(X_e)_{e \in E}$ on a common probability space and a real number $\lambda > 0$ such that $r(S) = \lambda H(X_S)$ for all $S \subseteq E$, where $X_S$ is the tuple $(X_e)_{e \in S}$ and $H$ is the Shannon entropy.

**Almost multilinear matroids.** A polymatroid $(E, \tilde r)$ is *linear* if $\tilde r(S) = \dim \sum_{e \in S} W_e$ for subspaces $W_e$ of a vector space over some field. A matroid $(E, r)$ is *almost multilinear* if for every $\varepsilon > 0$ there are a linear polymatroid $(E, \tilde r)$ and an integer $c \ge 1$ with $\max_{S \subseteq E} |r(S) - \tilde r(S)/c| < \varepsilon$.

Every linear matroid is multilinear and skew-linear, every multilinear matroid is entropic and almost multilinear, and there is a skew-linear matroid that is not multilinear (Theorem 6.1 of the second source below). [Algebraic matroids](../algebraic-matroids/is-algebraic.md) form a further class, defined through algebraic independence in field extensions.

## Depends on

- [Field](../../../Algebra/rings-and-fields/field.md)

## Proof depends on

None.

## Sources

- L. Kühne and G. Yashfe, "On entropic and almost multilinear representability of matroids", *Duke Mathematical Journal* 175 (2026), no. 8, 1363–1451, doi:10.1215/00127094-2025-0047; read as arXiv:2206.03465v3, <https://arxiv.org/abs/2206.03465v3>: Definitions 2.1 to 2.5 of arXiv:2206.03465v3.
- L. Kühne, R. Pendavingh and G. Yashfe, "Von Staudt constructions for skew-linear and multilinear matroids", *Combinatorial Theory* 3 (2023), no. 1, article 16, doi:10.5070/C63160429; read as arXiv:2012.07361v1, <https://arxiv.org/abs/2012.07361v1>: Definition 2.1 and the definitions following it in Section 2 of arXiv:2012.07361v1, and Theorem 6.1 there (a skew-linear matroid that is not multilinear).
