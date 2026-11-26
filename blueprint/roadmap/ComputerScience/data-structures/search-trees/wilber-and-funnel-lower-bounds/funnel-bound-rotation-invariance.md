# Rotation invariance of the funnel bound

For a permutation access sequence $X$ viewed as the point set $P(X)$ in the plane, let $X^{\circlearrowleft}$ be the access sequence whose point set is the image of $P(X)$ under a rotation by $90$ degrees (exchanging the roles of keys and times, with one axis reversed). Then $\mathrm{W2}(X^{\circlearrowleft}) = \Theta(\mathrm{W2}(X))$; in fact the funnel bound admits a symmetric characterization in terms of the point set alone, from which the invariance follows.

## Proof sketch

Lecomte and Weinstein express $\kappa_t$ as the number of alternations along the staircase of points visible from $(x_t, t)$ and rewrite the total as a count of certain configurations of point pairs in $P(X)$ that is symmetric in the two coordinates; the configurations are preserved by the rotation.

## Depends on

- [Wilber's funnel bound](funnel-bound.md)

## Proof depends on

- [Wilber's funnel bound](funnel-bound.md)

## Sources

- Victor Lecomte, Omri Weinstein, "Settling the Relationship Between Wilber's Bounds for Dynamic Optimality", ESA (2020), arXiv:1912.02858.
