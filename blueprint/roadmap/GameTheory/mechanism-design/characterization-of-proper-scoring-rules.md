# Characterization of proper scoring rules

Let $X$ be a finite outcome set and allow scores in $[-\infty, \infty)$. A scoring rule $S$ is regular if $S(q, w) > -\infty$ whenever $q(w) > 0$, and expected
scores $\mathbb{E}_{w \sim p} S(q, w)$ are taken with the convention $0 \cdot (-\infty) = 0$. Then a regular scoring rule is proper if and only if there are a
convex function $G : \Delta(X) \to \mathbb{R}$ and a selection $G^*$ of generalized subgradients of $G$ (vectors with entries in $[-\infty, \infty)$, finite on the
support of $q$, an entry $-\infty$ allowed only where $q(w) = 0$, satisfying $G(p) \ge G(q) + \langle G^*(q), p - q \rangle$ for all $p$) such that
$S(q, w) = G(q) - \langle G^*(q), q \rangle + G^*(q)_w$; it is strictly proper if and only if $G$ is strictly convex. Restricting to finite
subgradients gives a version valid only on the interior of the simplex or for rules with finite scores; the logarithmic rule needs the
extended convention at the boundary.

## Depends on

- [Scoring rules and properness for finite outcomes](remaining-clauses-of-scoring-rules-and-properness.md)

## Sources

- Strictly Proper Scoring Rules, Prediction, and Estimation — Gneiting and Raftery, JASA 102 (2007), Section 3.1, Definition 2 and Theorem 2 (McCarthy, Savage); Theorem 1 for general sample spaces. <https://stat.uw.edu/raftery/Research/PDF/Gneiting2007jasa.pdf>
