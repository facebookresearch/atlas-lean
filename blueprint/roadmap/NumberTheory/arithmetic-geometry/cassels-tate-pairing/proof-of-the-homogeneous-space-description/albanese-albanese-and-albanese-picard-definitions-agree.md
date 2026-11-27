# The Albanese–Albanese and Albanese–Picard definitions agree

Let $K$, $A$, $A^\vee$ and $\mathcal{P}$ be as in
[The Albanese–Albanese definition of the Cassels–Tate pairing](albanese-albanese-definition-of-the-cassels-tate-pairing.md), and
let $\langle\,,\rangle_A$ be the [Albanese–Picard definition](albanese-picard-definition-of-the-cassels-tate-pairing.md) for
$V = A$, computed with the same $\mathcal{P}$. Then for all $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$,

$$\langle a, a'\rangle_{\mathcal{P}} = \langle a, a'\rangle_A.$$

Proof (Poonen and Stoll). The transpose ${}^t\mathcal{P}$ maps $Z^0(A^\vee_{\bar K}) \to \operatorname{Div}^0(A_{\bar K})$ and induces the identity
$A^\vee \to \operatorname{Pic}^0_A = A^\vee$; it maps the exact sequence $0 \to Y^0(A^\vee_{\bar K}) \to Z^0(A^\vee_{\bar K}) \to A^\vee(\bar K) \to 0$ to
$0 \to \bar K(A)^\times/\bar K^\times \to \operatorname{Div}^0(A_{\bar K}) \to \operatorname{Pic}^0(A_{\bar K}) \to 0$, the first exact sequences of the two
definitions are the same, and the maps respect the two pairs of pairings: $[y, {}^t\mathcal{P}(z)] = \mathcal{P}(y, z)$, with the base
point $0$, and the function with divisor ${}^t\mathcal{P}(y')$ evaluated at $z$ is ${}^t\mathcal{P}(y', z)$. So the image of a lift
$\mathfrak{a}'$ for the Albanese–Albanese definition is a lift for the Albanese–Picard definition, and the cochains of the two
definitions agree.

Poonen and Stoll prove $\langle a, a'\rangle_D = \langle a, {}^tD\,a'\rangle_V$ for any divisor $D$ on a product $V \times W$; for a
Poincaré divisor on $A \times A^\vee$, ${}^t\mathcal{P}$ induces the identity of $A^\vee$, which gives the statement (their Remark after
Proposition 33).

## Depends on

- [The Albanese–Albanese definition of the Cassels–Tate pairing](albanese-albanese-definition-of-the-cassels-tate-pairing.md)
- [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md)

## Proof depends on

- [The Albanese–Picard pairing of zero-cycles and divisors](albanese-picard-pairing-of-zero-cycles-and-divisors.md), for $[y, {}^t\mathcal{P}(z)] = \mathcal{P}(y, z)$
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for the Poincaré bundle, through which ${}^t\mathcal{P}$ induces the identity of $A^\vee$ (its item 1)
- [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md), for the independence of the choices

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.3, Proposition 33, the Remark after it and its proof, p. 1146 ("If $V = A$ is an
  abelian variety, if $W = A^\vee$, and if $D \in \operatorname{Div}(A \times A^\vee)$ is a Poincaré divisor, then the induced homomorphism
  ${}^tD \colon A^\vee \to A^\vee$ is the identity").
