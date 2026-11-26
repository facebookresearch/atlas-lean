# Chemostat: the total substrate equivalent relaxes to the feed

For a well-mixed continuous fermentor (chemostat) with dilution rate $D$, feed substrate concentration $S_f$,
yield $y$ and specific growth rate $\mu$, the chemostat balances for biomass $X$ and substrate $S$ are

$$\frac{dX}{dt} = \bigl(\mu(S) - D\bigr) X, \qquad
\frac{dS}{dt} = D (S_f - S) - \frac{1}{y} \, \mu(S) X ,$$

the integral curves of the [chemostat vector field](vector-field.md). Here $D$, $S_f$ and $y$ are any real numbers and
$\mu : \mathbb{R} \to \mathbb{R}$ is any function, such as the Monod rate $\mu(S) = \mu_m S / (K_s + S)$; a
quotient by $0$ is read as $0$.

Let $I$ be an interval containing $0$ and let $(X, S)$ satisfy these balances on $I$, with derivatives taken within
$I$ (one-sided at an endpoint that $I$ contains). Then the [substrate equivalent](substrate-equivalent.md)
$Z = S + X / y$ satisfies

$$\frac{dZ}{dt} = D (S_f - Z) \quad \text{on } I,$$

hence $Z(t) = S_f + (Z(0) - S_f) \, e^{-D t}$ for every $t \in I$; if $D > 0$ and $I$ contains
$[0, \infty)$, then $Z(t) \to S_f$ as $t \to \infty$.

The growth terms cancel because biomass production consumes substrate in the fixed ratio $1/y$; the
identity uses only this common factor $\mu(S) X$, not the Monod form, so it needs no restriction on $\mu$ or on
the values of $S$ (for Monod growth the balances are usually considered where $S > -K_s$, so that $\mu(S)$ is
defined). The explicit form follows because $(Z(t) - S_f)\, e^{D t}$ has derivative $0$ on $I$.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 10.5, "Nonsegregated Fermentation Model", Equation 10.18 (the chemostat model with
  Monod growth, p. 596).
