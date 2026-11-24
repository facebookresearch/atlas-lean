# Differential privacy as hypothesis testing

Let $M$ be a randomized mechanism with output space $X$, and let $D_0$, $D_1$ be neighboring databases. For the test of $H_0$: the output $Y$ came from $D_0$ against $H_1$: $Y$ came from $D_1$, a rejection region $S \subseteq X$ has *false-alarm* probability $P_{\mathrm{FA}}(S) = \Pr[M(D_0) \in S]$ and *missed-detection* probability $P_{\mathrm{MD}}(S) = \Pr[M(D_1) \notin S]$. For $\varepsilon \ge 0$ and $\delta \in [0, 1]$, $M$ is $(\varepsilon, \delta)$-differentially private if and only if for all neighboring $D_0$, $D_1$ and all $S \subseteq X$

$$P_{\mathrm{FA}}(S) + e^{\varepsilon} P_{\mathrm{MD}}(S) \ge 1 - \delta \quad\text{and}\quad e^{\varepsilon} P_{\mathrm{FA}}(S) + P_{\mathrm{MD}}(S) \ge 1 - \delta.$$

Equivalently, with the privacy region $R(\varepsilon, \delta) = \{(P_{\mathrm{MD}}, P_{\mathrm{FA}}) : P_{\mathrm{FA}} + e^{\varepsilon} P_{\mathrm{MD}} \ge 1 - \delta,\ e^{\varepsilon} P_{\mathrm{FA}} + P_{\mathrm{MD}} \ge 1 - \delta\}$ and the privacy region $R(M)$ of the mechanism, the union over neighboring pairs of the convex hulls $R(M, D_0, D_1)$ of the points $(P_{\mathrm{MD}}(S), P_{\mathrm{FA}}(S))$, the mechanism $M$ is $(\varepsilon, \delta)$-differentially private if and only if $R(M) \subseteq R(\varepsilon, \delta)$. The convex hull contains the error pairs of every randomized decision rule.

## Depends on

- [Differential privacy](differentially-private.md)

## Sources

- P. Kairouz, S. Oh and P. Viswanath, "The composition theorem for differential privacy", *IEEE Transactions on Information Theory* 63(6):4037–4049, 2017, <https://kairouzp.github.io/p4_composition_theorem.pdf>, Section II, Theorem II.1, (2), (3), Remark II.2 and Corollary II.3
