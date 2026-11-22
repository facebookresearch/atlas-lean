# Representation of a sublinear functional, pointwise form

Let $V$ be a real vector space and let $E : V \to \mathbb{R}$ be subadditive,
$E(x + y) \le E(x) + E(y)$, and positively homogeneous, $E(cx) = c\,E(x)$ for all $c > 0$ and
$x \in V$. Then for every $x \in V$ there is a linear functional $f$ on $V$ with $f \le E$ and
$f(x) = E(x)$. The proof is the Hahn–Banach extension of $c x \mapsto c\, E(x)$ from the line
through $x$.

## Informally uses

- [Hahn–Banach theorem](../../../Analysis/banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/README.md): Peng's proof extends the functional $c x \mapsto c\, E(x)$ from the
  line through $x$ to the whole space under the sublinear bound $E$ (arXiv:1002.4546v1,
  Appendix A, Theorem 2.2, the real-vector-space form).

## Background

- [Legendre transform](../../large-deviations/legendre-transform/README.md): the same convex
  duality in its finite-dimensional, function form, $\Lambda^*(x) = \sup_\lambda (\lambda x - \Lambda(\lambda))$;
  a sublinear functional is the support function of the convex set of linear functionals it
  dominates.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter I, Theorem 2.1, first part.
