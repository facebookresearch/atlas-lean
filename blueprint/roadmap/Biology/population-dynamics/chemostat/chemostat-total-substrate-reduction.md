# Chemostat: the total substrate equivalent relaxes to the feed

For a well-mixed continuous fermentor (chemostat) with dilution rate $D > 0$, feed substrate concentration $S_f \ge 0$, yield $y > 0$ and Monod growth rate
$\mu(S) = \mu_m S / (K_s + S)$, $\mu_m, K_s > 0$, the chemostat balances for biomass $X$ and substrate
$S$ are

$$\frac{dX}{dt} = \bigl(\mu(S) - D\bigr) X, \qquad
\frac{dS}{dt} = D (S_f - S) - \frac{1}{y} \, \mu(S) X .$$

Let $I$ be an interval containing $0$ and let $(X, S)$ be differentiable on $I$, satisfy these balances
there and have $S(t) > -K_s$ for $t \in I$. Then the substrate equivalent $Z = S + X / y$ satisfies

$$\frac{dZ}{dt} = D (S_f - Z) \quad \text{on } I,$$

hence $Z(t) = S_f + (Z(0) - S_f) \, e^{-D t}$ for every $t \in I$; if $I$ contains $[0, \infty)$,
then $Z(t) \to S_f$ as $t \to \infty$.

The growth terms cancel because biomass production consumes substrate in the fixed ratio $1/y$; the
identity uses only this common factor $\mu(S) X$, not the Monod form. The explicit form follows because
$(Z(t) - S_f)\, e^{D t}$ has derivative $0$ on $I$.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 10.5, "Nonsegregated Fermentation Model", Equation 10.18 (the chemostat model with
  Monod growth, p. 596).
