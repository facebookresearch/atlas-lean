# The Albanese–Picard pairings of a homogeneous space and of its abelian variety agree

Let $K$, $A$ and $A^\vee$ be as in [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md),
and let $X$ be a principal homogeneous space of $A$ over $K$, with $\operatorname{Pic}^0(X_{\bar K})$ identified with $A^\vee(\bar K)$
and $Z^0(X_{\bar K}) \to A(\bar K)$ the summation map. Then for all $a \in \text{Ш}(K, A)$ and $a' \in \text{Ш}(K, A^\vee)$,

$$\langle a, a'\rangle_X = \langle a, a'\rangle_A.$$

Poonen and Stoll prove it for any geometrically integral, smooth, projective variety $V$ and its Albanese variety, for the morphisms $\varphi \colon V_{\bar K} \to A_{\bar K}$
given by base points, which induce isomorphisms independent of the base point that descend to $K$. Proof. A morphism
$\psi$ given by a base point pushes $0$-cycles forward from $X$ to $A$ and pulls divisors back from $A$ to $X$, and the
resulting trilinear pairings $Y^0(X_{\bar K}) \times \mathrm{AlbMor}(X, A) \times \operatorname{Div}^0(A_{\bar K}) \to \bar K^\times$ and
$Z^0(X_{\bar K}) \times \mathrm{AlbMor}(X, A) \times \bar K(A)^\times/\bar K^\times \to \bar K^\times$ agree, $\mathrm{AlbMor}(X, A)$ being the free
group on these morphisms. Take lifts $\mathfrak{a}$ of $\alpha$ to $Z^0(X_{\bar K})$ and $\mathfrak{a}'$ of $\alpha'$ to $\operatorname{Div}^0(A_{\bar K})$, chosen, with the local lifts below, so that every
pairing, push-forward and pull-back used is defined (Poonen and Stoll, §12, p. 1142), and
use $\varphi \cup \mathfrak{a}'$ for $\langle a, a'\rangle_X$ and $\mathfrak{a} \cup \varphi$ for $\langle a, a'\rangle_A$; then the two cocycles
$\eta$ agree, so one $\epsilon$ serves for both, and with $b_v \cup \varphi$ as the local lift for $A$ the cocycles $\gamma_v$ agree
formally.

## Depends on

- [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md)

## Proof depends on

- [The Albanese–Picard definition of the Cassels–Tate pairing](albanese-picard-definition-of-the-cassels-tate-pairing.md), for the independence of the choices
- [The Albanese–Picard pairing of zero-cycles and divisors](albanese-picard-pairing-of-zero-cycles-and-divisors.md), for its definition through a base point

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.3, Proposition 31 and its proof, pp. 1144–1145 ("For all
  $a \in \text{Ш}(\mathrm{Alb}^0_{V/k})$ and $a' \in \text{Ш}(\mathrm{Pic}^0_{A/k,\mathrm{red}})$, $\langle a, \varphi^* a'\rangle_V = \langle \varphi_* a, a'\rangle_A$").
