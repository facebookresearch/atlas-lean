# Hecke operators on cusp forms and Hecke endomorphisms of the Jacobian

Let $N$ be a positive integer, $\Gamma$ a group of level $N$, $J$ the Jacobian of the
[modular curve $X_\Gamma$](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/modular-curve-of-a-group-of-level-n.md), with $J(\mathbb{C})$ the Jacobian of
$\mathfrak{H}^*/\Gamma$, and let $\mu \colon S_2(\Gamma) \to D_J$ be the isomorphism of
[weight-two cusp forms with holomorphic $1$-forms](cusp-forms-as-one-forms-on-the-modular-jacobian.md). For
$\alpha \in \mathrm{GL}_2(\mathbb{Q})$ with $\det \alpha > 0$, let $[\Gamma \alpha \Gamma]_2$ be the operator on $S_2(\Gamma)$ of
[Hecke operators of level $N$](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-operators-of-level-n.md), and $\{\Gamma \alpha \Gamma\}$ the endomorphism of
$J$ of [Hecke endomorphisms](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-endomorphisms-of-the-modular-jacobian.md). Then

$$\mu \circ [\Gamma \alpha \Gamma]_2 = \delta\{\Gamma \alpha \Gamma\} \circ \mu,$$

with $\delta$ the pullback of [holomorphic $1$-forms](holomorphic-one-forms-and-tangent-space.md). Consequently, for
every $n \ge 1$, the Hecke operator $T_n$ and the Hecke endomorphism $\xi_n$ satisfy

$$\mu \circ T_n = \delta\xi_n \circ \mu, \qquad \text{that is}, \qquad \mu(g \mid T_n) = \delta\xi_n(\mu(g)) \quad (g \in S_2(\Gamma)).$$

In particular, if $f \in S_2(\Gamma)$ satisfies $f \mid T_n = a_n f$ for all $n$, then $\delta\xi_n$ maps $\mu(f)$ onto
$a_n \mu(f)$.

The first identity is the case $\Gamma' = \Gamma$ of Shimura's (1.3), which he states for a second group $\Gamma'$ of
level $M$, with its own Jacobian $J'$ and isomorphism $\mu'$, and for $\alpha \in \mathbb{R} \cdot \mathrm{GL}_2(\mathbb{Q})$ with
$\det(\alpha) > 0$, in the form $\mu \circ [\Gamma' \alpha \Gamma]_2 = \delta\{\Gamma' \alpha \Gamma\} \circ \mu'$.

## Depends on

- [Weight-two cusp forms as holomorphic $1$-forms on the modular Jacobian](cusp-forms-as-one-forms-on-the-modular-jacobian.md)
- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/modular-curve-of-a-group-of-level-n.md), for $J$
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-operators-of-level-n.md)
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-endomorphisms-of-the-modular-jacobian.md)
- [Holomorphic $1$-forms and tangent space of a complex abelian variety](holomorphic-one-forms-and-tangent-space.md), for $\delta$

## Proof depends on

- [Holomorphic $1$-forms and tangent space of a complex abelian variety](holomorphic-one-forms-and-tangent-space.md), for the behaviour of $\delta$ under sums and composition
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-operators-of-level-n.md), for $T_n = T_m T_q$
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-endomorphisms-of-the-modular-jacobian.md), for $\xi_n = \xi_m \xi_q$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the commutative diagrams (7.2.2) and (7.2.6) of Shimura's *Introduction*, from which (1.3) follows, as cited
  by Shimura (1973), p. 525;
- the passage from (1.3) to $\mu \circ T_n = \delta\xi_n \circ \mu$ through the definitions $T_n = T_m T_q$,
  $T_q = \sum_\beta [\Gamma \beta \Gamma]_2$, $\xi_n = \xi_m \xi_q$ and $\xi_q = \sum_\beta \{\Gamma \beta \Gamma\}$, with the order of
  composition fixed by the right action $g \mapsto g \mid T_n$ and the reversal of products by $\delta$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 ((1.3), "the commutative diagrams (7.2.2) and (7.2.6) of [11] imply", the definitions of
  $T_n$ and $\xi_n$, and $\mu \circ T_n = \delta\xi_n \circ \mu$); p. 526 ("By (1.3), we see that $\delta\xi_n$ maps $\mu(f)$
  onto $a_n \cdot \mu(f)$", in the proof of Theorem 1).
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publ. Math. Soc.
  Japan 11, Iwanami Shoten and Princeton University Press, 1971: (7.2.2), (7.2.6) and §3.4, as cited in Shimura (1973) above; not read for this page.
