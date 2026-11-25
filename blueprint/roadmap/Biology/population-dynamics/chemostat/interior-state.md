# Interior steady state of the chemostat

For the Monod growth rate $\mu(S) = \mu_m S / (K_s + S)$, the dilution rate $D$, the feed substrate
concentration $S_f$ and the yield $y$, the interior steady state is the state $(X^*, S^*)$ with

$$S^* = \frac{D K_s}{\mu_m - D}, \qquad X^* = y\, (S_f - S^*),$$

a quotient by $0$ being read as $0$. When $K_s > 0$ and $0 \le D < \mu_m$, $S^*$ is the substrate level at which
growth balances dilution, $\mu(S^*) = D$ ([where the Monod rate equals the dilution rate](mm-rate-eq-iff.md)).
For $\mu_m, K_s, S_f, y > 0$ and $0 < D < \mu(S_f)$ it is a steady state in the closed quadrant $X, S \ge 0$,
with $0 < S^* < S_f$ and $X^* > 0$.
