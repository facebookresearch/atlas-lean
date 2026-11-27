# The Albanese–Picard and homogeneous space definitions agree

Let $K$ be a number field, $A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over
$K$ with [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, $a \in \text{Ш}(K, A)$ and
$a' \in \text{Ш}(K, A^\vee)$. Let $X$ be a principal homogeneous space of $A$ over $K$ representing $a$, let $b'$ be the image of
$a'$, through $\operatorname{Pic}^0(X_{\bar K}) = A^\vee(\bar K)$, in $H^2(G_K, \bar K(X)^\times/\bar K^\times)$, let
$f' \in H^2(G_K, \bar K(X)^\times)$ lift $b'$, and let $c_v \in \mathrm{Br}(K_v)$ be the class whose image is $f'_v$, for every place $v$,
as in the [homogeneous space description](../homogeneous-space-description-of-the-cassels-tate-pairing.md). Then, with
$\langle\,,\rangle_A$ the [Albanese–Picard definition](albanese-picard-definition-of-the-cassels-tate-pairing.md) for $V = A$,

$$\langle a, a'\rangle_A = \sum_v \mathrm{inv}_v(c_v).$$

Proof (Poonen and Stoll). By the agreement of the Albanese–Picard pairings of $X$ and of $A$, it suffices to compute
$\langle a, a'\rangle_X$. Choose $P \in X(\bar K)$ and take $\mathfrak{a} = dP$, a cocycle with values in $Z^0(X_{\bar K})$, and a cochain
$\mathfrak{a}'$ with values in $\operatorname{Div}^0(X_{\bar K})$ representing $a'$; then $d\mathfrak{a}'$ is the divisor of a cocycle $f'$ with
values in $\bar K(X)^\times$, which represents a lift of $b'$. As $d\mathfrak{a} = 0$, $\eta = -dP \cup f' = d(-P \cup f')$, and one may take
$\epsilon = -P \cup f'$. At each place choose $Q_v \in X(K_v)$ and $b_v = P_v - Q_v$; then

$$\gamma_v = (dP_v - d(P_v - Q_v)) \cup \mathfrak{a}'_v - (P_v - Q_v) \cup f'_v + P_v \cup f'_v = Q_v \cup f'_v,$$

the evaluation of $f'_v$ at the point $Q_v$, whose class is $c_v$.

## Depends on

- [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md)
- [Vanishing of the third cohomology of the multiplicative group of a number field](../../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/vanishing-of-h3-of-the-multiplicative-group.md), for the lift $f'$
- [The Brauer group of a local field embeds in the second cohomology of the functions on a torsor with a point](brauer-group-into-functions-on-a-torsor-with-a-point.md), for the uniqueness of $c_v$

## Proof depends on

- [The Albanese–Picard pairings of a homogeneous space and of its abelian variety agree](albanese-picard-pairings-of-a-torsor-and-of-its-abelian-variety.md)
- [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md), for the independence of the choices
- [The Brauer group of a local field embeds in the second cohomology of the functions on a torsor with a point](brauer-group-into-functions-on-a-torsor-with-a-point.md), for computing $c_v$ by evaluation at a point of $X(K_v)$

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.3, Proposition 32 and its proof, pp. 1145–1146; §3.1, p. 1115, footnote 5 ("One can
  compute $c_v$ by evaluating $f'_v$ at a point in $X(k_v)$").
