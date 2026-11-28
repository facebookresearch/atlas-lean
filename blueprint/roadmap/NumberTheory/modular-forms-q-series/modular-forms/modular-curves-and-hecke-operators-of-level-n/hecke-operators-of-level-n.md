# Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$

Let $N$ be a positive integer and $\Gamma$ a group of level $N$, that is, a subgroup of
$\mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(N) \subset \Gamma \subset \Gamma_0(N)$, and let
$S_2(\Gamma)$ be the space of [cusp forms](cusp-form.md) of weight $2$ for $\Gamma$, with the slash action
$(f \mid_2 \alpha)(z) = \det(\alpha)\,(c z + d)^{-2} f(\alpha z)$ of
$\alpha = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{GL}_2(\mathbb{Q})$ with $\det \alpha > 0$,
where $\alpha z = (a z + b)/(c z + d)$: Shimura's $f \mid [\alpha]_2$, and the weight-$2$ slash action of the
[cusp form](cusp-form.md) page.

For such an $\alpha$, the double coset $\Gamma \alpha \Gamma$ is a finite disjoint union
$\Gamma \alpha \Gamma = \bigsqcup_\nu \Gamma \alpha_\nu$ of right cosets, and

$$f \mid [\Gamma \alpha \Gamma]_2 = \sum_\nu f \mid_2 \alpha_\nu \qquad (f \in S_2(\Gamma)),$$

which does not depend on the choice of the $\alpha_\nu$ and lies in $S_2(\Gamma)$. This is the
[Hecke operator](../hecke-operators/hecke-operator.md) $T(g)$ for $U = V = \Gamma$, $g = \alpha^{-1}$ and the
left action $\gamma \cdot f = f \mid_2 \gamma^{-1}$, restricted to $S_2(\Gamma)$: if
$\Gamma \alpha^{-1} \Gamma = \bigsqcup_i g_i \Gamma$, then $\Gamma \alpha \Gamma = \bigsqcup_i \Gamma g_i^{-1}$.

For a positive integer $n$, let $q$ be the largest divisor of $n$ prime to $N$ and $m = n / q$. Shimura's
**Hecke operator** $T_n$ on $S_2(\Gamma)$ is

$$T_n = T_m T_q, \qquad T_m = [\Gamma \alpha \Gamma]_2 \text{ with } \alpha = \begin{pmatrix} 1 & 0 \\ 0 & m \end{pmatrix}, \qquad T_q = \sum_\beta [\Gamma \beta \Gamma]_2,$$

the last sum over the distinct double cosets $\Gamma \beta \Gamma$ of matrices $\beta \in M_2(\mathbb{Z})$ with
$\det \beta = q$ and $\beta \equiv \begin{pmatrix} 1 & 0 \\ 0 & q \end{pmatrix} \pmod N$. In particular $T_1$
is the identity. A **normalized common eigenfunction** of the $T_n$ is an
$f(z) = \sum_{n \ge 1} a_n e^{2 \pi i n z}$ in $S_2(\Gamma)$ with $a_1 = 1$ and $f \mid T_n = a_n f$ for all
$n \ge 1$.

## Depends on

- [Cusp form](cusp-form.md), for $S_2(\Gamma)$
- [Congruence subgroup $\Gamma_0(N)$](congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](congruence-subgroup-gamma1.md)
- [Hecke operator](../hecke-operators/hecke-operator.md), for $[\Gamma \alpha \Gamma]_2$

## Proof depends on

This node has no prerequisites.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the finiteness of $\Gamma \backslash \Gamma \alpha \Gamma$ for $\alpha \in \mathrm{GL}_2(\mathbb{Q})$ with
  $\det \alpha > 0$, from the commensurability of $\Gamma$ and $\alpha^{-1} \Gamma \alpha$;
- that $[\Gamma \alpha \Gamma]_2$ maps $S_2(\Gamma)$ into itself: invariance, holomorphy and vanishing at
  the cusps of the sum;
- the finiteness of the set of double cosets $\Gamma \beta \Gamma$ in the definition of $T_q$, so that
  $T_q$ is a finite sum;
- the normalization of $[\Gamma \alpha \Gamma]_2$ as the sum of the $f \mid [\alpha_\nu]_2$, which is that of
  Shimura's *Introduction*, §3.4, and which Shimura's relation (1.3), $\mu \circ [\Gamma' \alpha \Gamma]_2 =
  \delta\{\Gamma' \alpha \Gamma\} \circ \mu'$ (p. 525), matches with the point map
  $[z] \mapsto \sum_\nu [\alpha_\nu z]$ of the [Hecke endomorphisms](hecke-endomorphisms-of-the-modular-jacobian.md).

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the definition of
  $T_n = T_m T_q$, $T_m = [\Gamma \alpha \Gamma]_2$ and $T_q = \sum_\beta [\Gamma \beta \Gamma]_2$, with
  $[\Gamma' \alpha \Gamma]_k$ the map $S_k(\Gamma') \to S_k(\Gamma)$ of [11, §3.4]); p. 526 (common
  eigenfunctions with $a_1 = 1$ and $f \mid T_n = a_n f$); §2, p. 527 (the definition
  $(f \mid [\alpha]_k)(z) = \det(\alpha)^{k/2} (c z + d)^{-k} f(\alpha(z))$).
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publ. Math. Soc.
  Japan 11, Iwanami Shoten and Princeton University Press, 1971: §3.4, as cited in Shimura (1973)
  above, for the operators $[\Gamma' \alpha \Gamma]_k$; not read for this page.
