# Number and stability of steady states of one-reaction flow networks

**Setting.** Consider the fully open network on species $X_1,\dots,X_n$

$$a_1X_1 + \dots + a_nX_n \xrightarrow{\ \ell\ } b_1X_1 + \dots + b_nX_n, \qquad X_i \underset{\kappa_i}{\overset{c_i}{\rightleftarrows}} 0 \quad (i = 1,\dots,n),$$

with mass-action steady-state equations $(b_i - a_i)\ell x^a - c_i x_i + \kappa_i = 0$. Let $\operatorname{sgn}(i) = \operatorname{sign}(b_i - a_i)$ and

$$a_+ = \sum_{\operatorname{sgn}(i) = 1} a_i, \qquad a_- = \sum_{\operatorname{sgn}(i) = -1} a_i.$$

After rescaling, the positive steady states correspond, with multiplicity, to the roots in an interval $(0,k_-)$ of the one-variable Gale dual equation $g(y) = h(y) - \kappa y$, where $h(y) = \prod_i (\operatorname{sgn}(i)\,y + k_i)^{a_i}$ for positive parameters $k_i, \kappa$.

**Theorem (number of steady states, irreversible case).** For all positive rate constants:

1. if $a_+ = 0$, there is exactly one positive steady state, and it is nondegenerate;
2. if $a_- = 0$ and $a_+ > 0$, there are at most two positive nondegenerate steady states if $a_+ > 1$ and at most one if $a_+ = 1$;
3. if $a_+ > 0$ and $a_- > 0$, there are at most three positive steady states if $a_+ > 1$ and exactly one otherwise; three occur exactly when $h'$ has a root $\xi \in (0,k_-)$, $h''$ has a root $y^* \in (0,\xi)$, and the tangent line to $h$ at $y^*$ is non-positive at $0$.

**Theorem (stability).**

1. Some rate constants give at least one asymptotically stable positive steady state.
2. If $a_+ > 1$ and $a_- = 0$, some rate constants give one asymptotically stable and one unstable positive steady state.
3. If $a_+ > 1$ and $a_- > 0$, some rate constants give two asymptotically stable and one unstable positive steady state (bistability).

**Theorem (reversible case).** If the non-flow reaction is reversible, $a \cdot X \rightleftarrows b \cdot X$, then for $a_+ > 1$ and $a_- = 0$ there are parameters with three nondegenerate positive steady states; for $a_+ > 0$ the number of roots of the reduced one-variable equation in $(0,k_-)$ is at most $\max(a_-, b_+ + b_- - a_+) + 2$; and if $a_+ > 1$ or $b_- > 1$, some parameters give two asymptotically stable and one unstable positive steady state.

## Depends on

- [Multistationarity of fully open networks with one non-flow reaction](../multistationarity-of-fully-open-networks/multistationarity-of-fully-open-networks-with-one-non-flow-reaction.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

The steady-state system has $n$ equations in $n$ unknowns but only $n+2$ distinct monomials, so it is a fewnomial system; Gale duality trades it for a single equation in one variable that preserves the number and multiplicity of positive solutions. Positive roots of $h(y) = \kappa y$ are intersections of a polynomial with only real roots (at $-\operatorname{sgn}(i)k_i$, of multiplicity $a_i$) and a line through the origin; the location of the roots of $h$ relative to $0$, governed by $a_+$ and $a_-$, and the convexity of $h$ on $(0,k_-)$ bound the number of intersections by $1$, $2$ or $3$. Stability follows by relating the sign of $g'$ at a root to the sign of the Jacobian determinant and tracking it as $\kappa$ moves the line across $h$. This refines the qualitative one-reaction criterion $a_+ > 1$ to exact counts and parameter regions.

## Sources

- Elisenda Feliu and Martin Helmer, "Multistationarity and Bistability for Fewnomial Chemical Reaction Networks", Bulletin of Mathematical Biology 81 (2019), 1089–1121, <https://doi.org/10.1007/s11538-018-00555-z>; numbering as in arXiv:1807.02991: Proposition 2.3, Theorems 3.4–3.6 and 3.13, Propositions 3.8–3.10 (Section 3), Propositions 4.4–4.6 and Theorem 4.9 (Section 4).
