# The black-box first-order oracle model

In the black-box model the convex constraint set $\mathcal{X} \subseteq \mathbb{R}^d$ is known and the convex objective $f : \mathcal{X} \to \mathbb{R}$ is accessed only through oracles. A *first-order oracle* takes a point $x \in \mathcal{X}$ and returns a subgradient of $f$ at $x$; a *zeroth-order oracle* returns $f(x)$. A *black-box first-order procedure* is a map from a history $(x_1, g_1, \ldots, x_t, g_t)$, with $g_s \in \partial f(x_s)$, to the next query point $x_{t+1}$. Computation other than oracle queries is not charged: the *oracle complexity* of a class of problems is the number of queries needed to find an $\varepsilon$-approximate minimizer of every function in the class.

A subclass used for lower bounds is the span-restricted procedures, with $x_1 = 0$ and $x_{t+1} \in \mathrm{Span}(g_1, \ldots, g_t)$. The related [lower complexity bound for smooth convex minimization](exists-lower-bound-smooth-convex.md) quantifies over sequences with $x_j - x_0$ in the span of earlier gradients of a smooth function. It shifts by $x_0$ and uses gradients rather than subgradients, so recording it as an instance of this model needs a clause-by-clause comparison first.

## Depends on

- [Subdifferential of a convex function](../subdifferential-calculus/convex-subdifferential.md)

## Expansion

This node is not ready to be stated as one definition. A good expansion fixes:

- The initial point: a fixed $x_1$, a given $x_0$ as for the related bound, or a choice of the procedure
- The output rule: the last query, the best query so far, or a separate output map from the history
- The accuracy and termination conventions: $\varepsilon$-accuracy in function value against $\inf f$ or against a given minimizer, and whether the procedure must stop after a fixed number of queries or report its own termination
- Whether the oracle may choose among subgradients (a resisting oracle), as lower-bound arguments require

## Proof depends on

Definition only; no proof prerequisites.

## Sources

- Sébastien Bubeck, "Convex Optimization: Algorithms and Complexity", Foundations and Trends in Machine Learning 8(3–4), 2015, arXiv:1405.4980: Section 1.4 (black-box model, zeroth- and first-order oracles, oracle complexity) and Section 3.5 (a black-box procedure maps the history to the next query point; assumption (3.15) for the span-restricted subclass).
