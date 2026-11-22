# Geodesic metric space

A pseudometric space $X$ is geodesic if any two points $x, y$ are joined by a geodesic segment: a map $\gamma : \mathbb{R} \to X$ with $\gamma(0) = x$, $\gamma(d(x, y)) = y$ and $d(\gamma s, \gamma t) = |s - t|$ for $s, t \in [0, d(x, y)]$.

A segment between two points at distance $0$ is constant, so a pseudometric space with two distinct points at distance $0$ is never geodesic: the notion is meant for metric spaces. These segments realise the distance globally, unlike the local geodesics of this topic, which only realise it near each time. Real normed spaces are geodesic, and so is every connected complete Riemannian manifold (Hopf–Rinow, Gromov's 1.6.A: between any two points of such a manifold there is a minimising geodesic). Geodesic spaces are the setting of the thin-triangle description of hyperbolicity and of the Švarc–Milnor lemma.

## Background

- [Hopf–Rinow theorem](../../riemannian-geometry/hopf-rinow-theorem/hopf-rinow.md): the equivalence of geodesic and metric completeness; the full theorem also gives minimising geodesics between any two points of a complete connected Riemannian manifold, making it a geodesic space.

## Sources

- M. Gromov, *Hyperbolic groups*, in *Essays in Group Theory* (S. M. Gersten, ed.), Math. Sci. Res. Inst. Publ. 8, Springer, 1987, 75–263, §1.6.
