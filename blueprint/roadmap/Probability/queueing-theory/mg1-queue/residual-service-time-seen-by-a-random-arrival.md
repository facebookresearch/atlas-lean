# Residual service time seen by a random arrival

Let $B \ge 0$ have distribution function $F_B$ with $0 < E[B] < \infty$. The *equilibrium residual time* $R$ of $B$ is the random variable with density

$$
f_R(t) = \frac{1 - F_B(t)}{E[B]}, \qquad t \ge 0 ,
$$

which is a probability density since $\int_0^\infty (1 - F_B(t))\,dt = E[B]$. Its moments are

$$
E[R^n] = \frac{E[B^{n+1}]}{(n + 1)E[B]}, \qquad \text{in particular} \quad E[R] = \frac{E[B^2]}{2E[B]} ,
$$

by Fubini's theorem, both sides possibly infinite. For exponential $B$, $R$ has the same law as $B$. The source interprets $R$ as the remaining service time seen at a time chosen uniformly in a long stretch of back-to-back services: the service in progress has the size-biased law $x\,dF_B(x)/E[B]$ (with density $x f_B(x)/E[B]$ when $B$ has a density $f_B$) and the time is uniform within it. That interpretation is a statement about renewal processes, proved with the [renewal-reward theorem](../../point-processes/renewal-processes/renewal-reward-theorem.md), and is not part of this page.


## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Section 7.7 (the derivation of $f_X$, $f_R$ and the moments of $R$).
