# Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$

Let $N$ be a positive integer. A **group of level $N$** is a subgroup $\Gamma$ of
$\mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(N) \subset \Gamma \subset \Gamma_0(N)$. Such a $\Gamma$ acts by linear
fractional transformations on $\mathfrak{H}^* = \mathfrak{H} \cup \mathbb{P}^1(\mathbb{Q})$, the union of the
upper half-plane and the cusps, and the quotient $\mathfrak{H}^*/\Gamma$, with its usual complex structure
(local parameters at the cusps and at the elliptic points), is a compact Riemann surface.

The **modular curve** $X_\Gamma$ is Shimura's **standard model** of $\mathfrak{H}^*/\Gamma$ over $\mathbb{Q}$:
the curve $V_S$ over $\mathbb{Q}$ of his *Introduction to the arithmetic theory of automorphic
functions*, §7.3 (p. 155), for the subgroup $S = \mathbb{Q}^\times U_N \Gamma$ of the adelic group
$\mathrm{GL}_2(\mathbb{A})$, where
$$U_N = \Bigl\{x \in \prod_p \mathrm{GL}_2(\mathbb{Z}_p) \times \mathrm{GL}_2(\mathbb{R})^+ \;\Bigm|\;
x_p \equiv \begin{pmatrix} * & 0 \\ * & 1 \end{pmatrix} \pmod N \text{ for every } p\Bigr\},$$
together with its identification of the compact Riemann surface $V_S(\mathbb{C})$ with
$\mathfrak{H}^*/\Gamma$. It is a curve over $\mathbb{Q}$, that is, a $\mathbb{Q}$-scheme that is proper,
smooth of relative dimension $1$ and geometrically irreducible. A curve over $\mathbb{Q}$ with an
isomorphism of its complex points with $\mathfrak{H}^*/\Gamma$ is not determined by that isomorphism
(a quadratic twist of an elliptic curve over $\mathbb{Q}$ has the same complex points), so
$X_\Gamma$ means this particular curve $V_S$. The Jacobian of $X_\Gamma$ is Shimura's jacobian
variety $J$ of $\mathfrak{H}^*/\Gamma$, which is so "naturally defined over $\mathbb{Q}$".

## Depends on

- [Congruence subgroup $\Gamma_0(N)$](congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](congruence-subgroup-gamma1.md)

## Proof depends on

This node has no prerequisites.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the compact Riemann surface $\mathfrak{H}^*/\Gamma$ of a finite-index subgroup $\Gamma$ of
  $\mathrm{SL}_2(\mathbb{Z})$: the topology of $\mathfrak{H}^*$, the charts at the cusps and the elliptic
  points, compactness and connectedness;
- the field of modular functions of level $N$ and the action of $\mathrm{GL}_2(\mathbb{A}_f)$ on it
  (Shimura's *Introduction*, §6), from which the curve $V_S$ over $\mathbb{Q}$ is defined (§7.3), with
  the identification of $V_S(\mathbb{C})$ with $\mathfrak{H}^*/\Gamma$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §0, p. 523 (groups of level
  $N$, $\mathfrak{H}^*$ and the jacobian variety $J$ of $\mathfrak{H}^*/\Gamma$); §1, p. 526 ("As shown in
  [11, §7.3], there is a 'standard model' of $\mathfrak{H}^*/\Gamma$ defined over $\mathbb{Q}$ (see also §4
  below), so that $J$ can naturally be defined over $\mathbb{Q}$"); §4, pp. 532–533 (the groups $U_N$
  and $S = \mathbb{Q}^\times U_N \Gamma$, defined "using the notation of [11, §7.3]", and "we take
  $V_S$ … of [11, p. 155] as models of $\mathfrak{H}^*/\Gamma$").
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publ. Math. Soc.
  Japan 11, Iwanami Shoten and Princeton University Press, 1971: §7.3 and p. 155, as cited in
  Shimura (1973) above.
