# Polynomial growth is a quasi-isometry invariant

Let $P$ and $Q$ be finite generating families of groups $G$ and $H$, and let $f : G \to H$ be a quasi-isometric embedding for the left-invariant word metrics: $|g^{-1} g'|_P \le L\, |f(g)^{-1} f(g')|_Q + C$ and $|f(g)^{-1} f(g')|_Q \le L\, |g^{-1} g'|_P + C$ for all $g, g'$. If $Q$ has polynomial growth, so does $P$. The map $f$ need not be a homomorphism, injective, or coarsely surjective.

The ball of radius $n$ of $G$ maps into a ball of radius $L' n + C'$ around $f(1)$, with $L' = \lceil L \rceil$ and $C' = \lceil C \rceil$, and each fibre of $f$ lies in a translate of the ball of radius $C'$; so $\gamma_P(n) \le \gamma_Q(L'n + C')\, \gamma_P(C')$. Hence quasi-isometric finitely generated groups have polynomial growth together, which is how Gromov combines his theorem with quasi-isometry: a finitely generated group quasi-isometric to a nilpotent group is virtually nilpotent.

## Background

- [Quasi-isometric embedding](../../../Geometry/metric-geometry/quasi-isometries/is-quasi-isometric-embedding.md): the general metric notion, here written out for word metrics.
- [Gromov's polynomial growth theorem](virtually-nilpotent-of-has-polynomial-gr.md): the theorem that turns this invariance into the quasi-isometric rigidity of virtually nilpotent groups.

## Sources

- M. Gromov, *Infinite groups as geometric objects*, Proceedings of the International Congress of Mathematicians, Warszawa 1983, vol. 1, 385–392, §2.B ("virtually nilpotent groups are characterized by the polynomial growth property which is q.i. invariant").
