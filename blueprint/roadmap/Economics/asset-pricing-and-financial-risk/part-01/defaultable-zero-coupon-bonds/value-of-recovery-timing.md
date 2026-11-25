# Effect of paying recovery at default instead of at maturity

Let $Q$ be a probability measure, $\tau \ge 0$ a random default time, $T \ge 0$, $D$ a deterministic discount function that is Borel, positive and bounded on $[0, T]$, $F \ge 0$ a face amount and $\rho \ge 0$ a recovery amount (for a recovery fraction $R$, take $\rho = FR$). Compare two contracts that both pay $F$ at $T$ on $\{\tau > T\}$: in the first, $\rho$ is paid at the default time on $\{0 \le \tau \le T\}$; in the second, $\rho$ is paid at $T$ on $\{\tau \le T\}$. Their values differ by $V_{\mathrm{default}} - V_{\mathrm{maturity}} = \rho\,E_Q[(D(\tau) - D(T))\mathbf 1\{0 \le \tau \le T\}]$, since the survivor payments cancel; default at time $0$ is paid in both contracts. If $D$ is nonincreasing on $[0, T]$ the difference is nonnegative; for an arbitrary $D$ it need not be.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
