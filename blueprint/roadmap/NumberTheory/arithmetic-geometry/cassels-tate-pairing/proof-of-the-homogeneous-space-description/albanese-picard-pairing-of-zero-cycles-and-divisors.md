# The Albanese–Picard pairing of zero-cycles and divisors

Let $k$ be a field of characteristic $0$ with algebraic closure $\bar k$, $A$ an
[abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $k$ with
[dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$, $\mathcal{P}$ a
[Poincaré divisor](../construction-of-the-cassels-tate-pairing/weil-pairing-through-a-poincare-divisor.md) on
$A \times A^\vee$, and let $V$ be $A$ or a principal homogeneous space $X$ of $A$ over $k$. Let $Z^0(V_{\bar k})$ and
$Y^0(V_{\bar k})$ be the groups of $0$-cycles of degree $0$ and of those summing to $0$, as in
[Lang's reciprocity law](../construction-of-the-cassels-tate-pairing/lang-reciprocity-law.md), and identify
$\operatorname{Pic}^0(V_{\bar k})$ with $A^\vee(\bar k)$: for $V = X$, a trivialization $A_{\bar k} \to X_{\bar k}$, $Q \mapsto P + Q$,
identifies $\operatorname{Pic}^0(X_{\bar k})$ with $\operatorname{Pic}^0(A_{\bar k}) = A^\vee(\bar k)$, independently of $P \in X(\bar k)$ and
$G_k$-equivariantly, since translations act trivially on $\operatorname{Pic}^0(A_{\bar k})$. There are $G_k$-equivariant exact sequences

$$0 \to Y^0(V_{\bar k}) \to Z^0(V_{\bar k}) \to A(\bar k) \to 0, \qquad 0 \to \bar k(V)^\times/\bar k^\times \to \operatorname{Div}^0(V_{\bar k}) \to A^\vee(\bar k) \to 0.$$

Choose $P_0 \in V(\bar k)$, let $\varphi \colon V_{\bar k} \to A_{\bar k}$ be $x \mapsto x - P_0$, and
$\mathcal{P}_0 = (\varphi \times 1)^* \mathcal{P}$ on $V \times A^\vee$. For $y \in Y^0(V_{\bar k})$ and $D' \in \operatorname{Div}^0(V_{\bar k})$,
choose $z' \in Z^0(A^\vee_{\bar k})$ summing to the class of $D'$; then $D' - {}^t\mathcal{P}_0(z')$ is the divisor of a function
$f'$ on $V_{\bar k}$, and the **Albanese–Picard pairing** is

$$[y, D'] = f'(y)\,\mathcal{P}_0(y, z') \in \bar k^\times,$$

defined when the terms are: $[\,,]$ is a partially defined pairing, and so are the evaluations below; the cycles and
divisors are always chosen so that the terms used are defined, which is always possible. The second pairing is evaluation, $Z^0(V_{\bar k}) \times \bar k(V)^\times/\bar k^\times \to \bar k^\times$,
$(z, f) \mapsto f(z)$, which does not depend on the constant in $f$; on $Y^0(V_{\bar k}) \times \bar k(V)^\times/\bar k^\times$ the two
agree, as $[y, (f)] = f(y)$ with $z' = 0$.

The pairing $[\,,]$ does not depend on $z'$, $\mathcal{P}$ or $P_0$, and so is $G_k$-equivariant. Changing $z'$ by
$y' \in Y^0(A^\vee_{\bar k})$ changes it by ${}^t\mathcal{P}_0(y', y)^{-1}\mathcal{P}_0(y, y') = 1$, by Lang's reciprocity law; changing
$\mathcal{P}$ by the divisor of a function $F$ multiplies both terms by inverse values of $F$ at $\varphi(y) \times z'$; changing
it by the pull-back of a divisor on $A^\vee$ changes nothing; and by the seesaw principle a change of $P_0$, which
translates $\mathcal{P}_0$ by a point $(a, 0)$, changes $\mathcal{P}_0$ by a divisor of these two kinds.

## Depends on

- [Abelian scheme](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $A^\vee(\bar k) = \operatorname{Pic}^0(A_{\bar k})$ (its item 1)
- [The Weil pairing through a Poincaré divisor](../construction-of-the-cassels-tate-pairing/weil-pairing-through-a-poincare-divisor.md), for Poincaré divisors and the values $\mathcal{P}(y, z')$
- [Theorem of the cube, theorem of the square and the seesaw principle](../../../../AlgebraicGeometry/abelian-varieties/theorem-of-the-cube.md), for the trivial action of translations on $\operatorname{Pic}^0(A_{\bar k})$, which makes the identification for $X$ independent of the point

## Proof depends on

- [Lang's reciprocity law for divisors on a product](../construction-of-the-cassels-tate-pairing/lang-reciprocity-law.md), for the independence of $z'$
- [Theorem of the cube, theorem of the square and the seesaw principle](../../../../AlgebraicGeometry/abelian-varieties/theorem-of-the-cube.md), for the independence of $P_0$

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §3.2, "The Albanese-Picard definition", pp. 1115–1117 (the partially defined pairing (2), for any geometrically integral, smooth, projective
  variety $V$ with $A = \mathrm{Alb}^0_V$ and $A' = \mathrm{Pic}^0_{V,\mathrm{red}}$, its independence of choices, p. 1116, the exact sequences (3) and the pairings (4), pp. 1116–1117); §2, pp. 1113–1114
  (the identification $\mathrm{Pic}^0_{X/k} = A^\vee$ for a principal homogeneous space).
