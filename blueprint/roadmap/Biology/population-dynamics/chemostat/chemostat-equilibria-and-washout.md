# Chemostat equilibria and the washout threshold

For the chemostat with dilution rate $D > 0$, feed substrate concentration $S_f > 0$, yield $y > 0$ and Monod growth rate
$\mu(S) = \mu_m S / (K_s + S)$, $\mu_m, K_s > 0$, the chemostat balances for biomass $X$ and substrate
$S$ are

$$\frac{dX}{dt} = \bigl(\mu(S) - D\bigr) X, \qquad
\frac{dS}{dt} = D (S_f - S) - \frac{1}{y} \, \mu(S) X ,$$

and their steady states are the zeros of the [chemostat vector field](vector-field.md).

Let $D_c = \mu(S_f) = \mu_m S_f / (K_s + S_f)$, the critical dilution rate; note $0 < D_c < \mu_m$. In
the closed quadrant $X \ge 0$, $S \ge 0$:

- the washout state $(X, S) = (0, S_f)$ is a steady state for every $D > 0$;
- if $D \ge D_c$, it is the only steady state;
- if $D < D_c$, there is exactly one further steady state, the [interior steady state](interior-state.md)

    $$S^* = \frac{D K_s}{\mu_m - D}, \qquad X^* = y \, (S_f - S^*),$$

    and it satisfies $0 < S^* < S_f$ and $X^* > 0$.

As $D$ increases to $D_c$, $S^* \to S_f$ and $X^* \to 0$, so the two steady states coalesce at
$D = D_c$. The formula for $S^*$ is used only for $D < D_c$, where $\mu_m - D > 0$.

A steady state has $X(\mu(S) - D) = 0$: either $X = 0$, and then $S = S_f$, or $\mu(S) = D$, which on
$S \ge 0$ has the unique solution $S^*$ when $D < \mu_m$ and none when $D \ge \mu_m$; the substrate
balance then gives $X = y(S_f - S^*)$, which is positive exactly when $D < D_c$ and is $0$ at
$D = D_c$, where the state is washout itself.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 10.5, Equations 10.18–10.19 and the critical dilution rate
  $D_c = \mu_m S_f / (K_s + S_f)$ with the discussion of the washout steady state (pp. 596–597).
