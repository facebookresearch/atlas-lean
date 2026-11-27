# Interior steady state of the chemostat

For the Monod growth rate $\mu(S) = \mu_m S / (K_s + S)$, the dilution rate $D$, the feed substrate
concentration $S_f$ and the yield $y$, the interior steady state is the state $(X^*, S^*)$ with

$$S^* = \frac{D K_s}{\mu_m - D}, \qquad X^* = y\, (S_f - S^*),$$

a quotient by $0$ being read as $0$. The substrate level $S^*$ is the
[steady-state concentration](../../pharmacokinetics/saturable-michaelis-menten-elimination/steady-conc.md) of
saturable elimination at infusion rate $D$: for $\mu_m, K_s > 0$ and $D < \mu_m$, growth
[balances dilution](../../pharmacokinetics/saturable-michaelis-menten-elimination/mm-rate-steady-conc.md)
there, $\mu(S^*) = D$, and, by the
[uniqueness of the steady state](../../pharmacokinetics/saturable-michaelis-menten-elimination/eq-steady-conc-of-mm-rate-eq.md),
any $S \ge 0$ with $\mu(S) = D$ equals $S^*$. For $\mu_m, K_s, S_f, y > 0$ and $0 < D < \mu(S_f)$ the state is
a steady state in the closed quadrant $X, S \ge 0$, with $0 < S^* < S_f$ and $X^* > 0$.
