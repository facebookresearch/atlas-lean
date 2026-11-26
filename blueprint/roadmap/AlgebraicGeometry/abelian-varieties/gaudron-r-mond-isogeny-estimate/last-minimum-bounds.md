# Bounds for the last minima of the lattices of homomorphisms

Let $k$ be a number field and $A$, $A'$ [abelian varieties](../abelian-scheme.md) over $k$, with $g =
\dim A$, isogenous over an extension $K$ of $k$. Let $k_1$ be the smallest extension of $k$ over
which all endomorphisms of $A \times A'$ are defined, and suppose $k \subset K \subset k_1$. Choose a
maximal family $A_1, \dots, A_t$ of abelian subvarieties of $A$ defined over $K$, simple over $K$ and
pairwise non-isogenous over $K$, so that $A$ is isogenous over $K$ to $A'' = \prod_{i=1}^t
A_i^{n_i}$ for integers $n_i \ge 1$ ([Poincaré's complete reducibility
theorem](../poincare-reducibility.md)). For each $i$ choose an isogeny over $k_1$ between $A_i$ and a
product $\prod_{j=1}^{u_i} C_{i,j}^{m_{i,j}}$ of powers of abelian varieties $C_{i,j}$ simple over
$k_1$ and pairwise non-isogenous, and put $A''' = \prod_{i=1}^t \prod_{j=1}^{u_i} C_{i,j}^{n_i
m_{i,j}}$, isogenous to $A$ over $k_1$. Let

$$M = \max\bigl(h_F(A), h_F(A'), h_F(A''), h_F(A'''), 1\bigr), \qquad P = 4 (9g)^{4g} (8g)^{64 g^2}
[k : \mathbb{Q}] \max\Bigl(M + \frac{3}{2} g, \log\bigl(4 (9g)^{4g} [k : \mathbb{Q}]\bigr)\Bigr)^2,$$

with $h_F$ the [stable Faltings height](../stable-faltings-height/faltings-height.md), and let $Z(C)
= (C \times \widehat C)^4$ and $\nu$ be as in the [construction of an abelian subvariety from the
period theorem](abelian-subvariety-from-the-period-theorem.md). Then:

1. For $C$ one of the $C_{i,j}$, $C'$ one of $A$, $A'$, $A_i$, and any principal polarizations of
   $Z(C)$ and $Z(C')$,

    $$\Lambda\bigl(\operatorname{Hom}_{k_1}(Z(C), Z(C'))\bigr) \le 2^{-30} P^{16 \nu(C')}.$$

2. For the last minima $\Lambda$, $\Lambda'$, $\Lambda_i$ of [isogeny degrees from last
   minima](isogeny-degree-from-last-minima.md), formed over $K$ with this choice of $A_1, \dots, A_t$,

    $$\Lambda_i \le (9g)^{4g} P^{32 \nu(A_i)} \qquad \text{and} \qquad \Lambda \Lambda' \le
    2^{-116} (9g)^{8g} P^{64 \nu(A)}.$$

All last minima are for the [Rosati metrics](rosati-metric-on-homomorphisms.md) of the principal
polarizations.

## Expansion

Item 1 is the [bound for the last minimum from an abelian
subvariety](last-minimum-from-an-abelian-subvariety.md) applied to the abelian subvariety $H \subset
Z(C) \times Z(C')^{128 \dim C'}$ of the [period theorem
construction](abelian-subvariety-from-the-period-theorem.md) over $k_1$, with $\deg Z(C) = (\dim
Z(C))! \ge 2^{15}$, $[k_1 : \mathbb{Q}] \le 4(9g)^{4g} [k : \mathbb{Q}]$, and the heights $h_F(C),
h_F(C') \le M + \frac{3}{2} g$, obtained from $h_F(C_{i,j}) \ge -\frac{3}{2} \dim C_{i,j}$ and the
additivity of $h_F$ on $A'''$ and $A''$. Item 2 follows from item 1 by the Galois trace argument
$\Lambda(\operatorname{Hom}_K(A, B)) \le [K_1 : K]\, \Lambda(\operatorname{Hom}_{K_1}(A, B))$ for a
finite Galois extension $K_1/K$ (Lemme 3.3), the submultiplicativity $\Lambda(\operatorname{Hom}_K(A,
B)) \le \Lambda(\operatorname{Hom}_K(A, C))\, \Lambda(\operatorname{Hom}_K(C, B))$ when $A$ or $B$ is
isogenous to an abelian subvariety of $C$ (Lemme 3.4, from $|\psi \circ \varphi| \le |\psi|
|\varphi|$, Proposition 2.7), the isometry given by the Rosati involution between
$\operatorname{Hom}_{k_1}(Z(A''), Z(A'''))$ and $\operatorname{Hom}_{k_1}(Z(A'''), Z(A''))$ for
principal polarizations (p. 2066), and the orthogonal decomposition of
$\operatorname{Hom}_{k_1}(Z(A'''), Z(A))$ into copies of the lattices
$\operatorname{Hom}_{k_1}(Z(C_{i,j}), Z(A))$. A good expansion has pages for Lemmes 3.3 and 3.4 and
Proposition 2.7, and states item 1 and item 2 as separate pages if the bookkeeping warrants it.

## Depends on

- [Rosati metric on lattices of homomorphisms](rosati-metric-on-homomorphisms.md), for the last
  minima
- [Abelian subvariety of bounded degree from the period theorem](abelian-subvariety-from-the-period-theorem.md),
  for $Z(C)$ and the invariant $\nu$
- [Isogeny degrees from last minima](isogeny-degree-from-last-minima.md), for $\Lambda$,
  $\Lambda'$ and $\Lambda_i$
- [Poincaré's complete reducibility theorem](../poincare-reducibility.md), for the decompositions
  $A''$ and $A'''$
- [Stable Faltings height](../stable-faltings-height/faltings-height.md), for $M$ and $P$
- [Zarhin's trick](../zarhin-trick.md), for the principal polarizations of $Z(C)$ and $Z(C')$

## Proof depends on

- [Last minimum of a lattice of homomorphisms from an abelian subvariety](last-minimum-from-an-abelian-subvariety.md)
- [Abelian subvariety of bounded degree from the period theorem](abelian-subvariety-from-the-period-theorem.md),
  over $k_1$, where all endomorphisms are defined
- [Field of definition of the endomorphisms of a product of isogenous abelian
  varieties](silverberg-field-of-definition.md), for $[k_1 : k] \le 4(9g)^{4g}$ and the Galois
  extension $k_1/K$
- [Bost's lower bound for the Faltings height](../stable-faltings-height/bost-lower-bound.md), for
  $h_F(C_{i,j}) \ge -\frac{3}{2} \dim C_{i,j}$
- [Raynaud's estimate for the Faltings height under
  isogeny](../stable-faltings-height/raynaud-isogeny-height-estimate.md), item 2, for $h_F(A''') =
  \sum_{i,j} n_i m_{i,j} h_F(C_{i,j})$ and the analogue for $A''$

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: §9, pp. 2097–2099 (the setting, pp. 2097–2098; $M$
  and $P$, p. 2098; Lemme 9.1 with its proof, p. 2098; Lemme 9.2, p. 2098, with its proof, p. 2099);
  Lemmes 3.3 and 3.4, pp. 2070–2071; Proposition 2.7 and the isometry before it, p. 2066.
