# Residual service time seen by a random arrival

Let $B \ge 0$ have distribution function $F_B$ with $0 < E[B] < \infty$. The *equilibrium residual time* $R$ of $B$ is the random variable with density

$$
f_R(t) = \frac{1 - F_B(t)}{E[B]}, \qquad t \ge 0 ,
$$

the law of the remaining service time of the customer in service seen at a time chosen uniformly in a long stretch of back-to-back services: the service in progress is length-biased, with density $x f_B(x)/E[B]$, and the arrival is uniform within it. Its moments are

$$
E[R^n] = \frac{E[B^{n+1}]}{(n + 1)E[B]}, \qquad \text{in particular} \quad E[R] = \frac{E[B^2]}{2E[B]} .
$$

For exponential $B$, $R$ has the same law as $B$.

## Expansion

This page becomes ready once its statement is fixed as the moment identity for the density $f_R$ alone, with the arrival interpretation moved to a separate page on length-biased sampling in a renewal process, whose proof needs the [renewal-reward theorem](../../point-processes/renewal-processes/renewal-reward-theorem.md); the source derives the interpretation heuristically.

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.7 (the derivation of $f_X$, $f_R$ and the moments of $R$).
