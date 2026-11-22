# Multiplicity from the translated coefficients

If the [translate](shift.md) $Q(X + a, Y + b)$ has no monomial of total degree less than $r$, then
$Q$ has a [root of multiplicity](has-root-mult.md) at least $r$ at $(a, b)$, that is
$Q \in (X - a, Y - b)^r$.

Every monomial $X^i Y^j$ with $i + j \ge r$ lies in $(X, Y)^r$, so the translate lies in
$(X, Y)^r$; translating back by $(-a, -b)$ carries $(X, Y)$ into $(X - a, Y - b)$. This is the
direction of the equivalence with Definition 12.2.9 of Guruswami, Rudra and Sudan that the
[interpolation step](exists-interpolant.md) needs.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Definitions 12.2.8 and 12.2.9.
