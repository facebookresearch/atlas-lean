# Targeted immunisation thresholds for the contact process on power-law Galton–Watson trees

**Setting.** The contact process (SIS infection) on a locally finite graph: each infected vertex recovers at rate $1$ and infects each healthy neighbour at rate $\lambda > 0$. Let $G$ be a supercritical Galton–Watson tree whose offspring law $X$ satisfies $P(X \ge k) \sim c_\star k^{2-\tau}$ for some $c_\star > 0$ and power-law exponent $\tau > 2$, and start with only the root infected. Without intervention the survival probability is positive for every $\lambda > 0$ and, as $\lambda \to 0$,

$$
P_{\mathrm{surv}}(\lambda) = \begin{cases}
\Theta\bigl(\lambda^{\frac{\tau-2}{3-\tau}}\bigr), & \tau \le 2.5,\\
\Theta\bigl(\lambda^{2\tau-4}/\log^{\tau-2}(1/\lambda)\bigr), & 2.5 < \tau \le 3,\\
\Theta\bigl(\lambda^{2\tau-4}/\log^{2\tau-4}(1/\lambda)\bigr), & \tau > 3.
\end{cases}
$$

*Targeted immunisation* at level $T$ removes every vertex with more than $T$ offspring (together with its descendants); *truncation* replaces $X$ by $X\mathbf{1}_{X \le T}$. Write $P^T_{\mathrm{surv}}(\lambda)$ for the survival probability, with $T = T(\lambda) \to \infty$ as $\lambda \to 0$.

**Statement.** For all sufficiently small $\lambda$, and identically for immunisation and truncation:

1. If $\tau < 2.5$, with $\rho_c = \bigl((3-\tau)/((\tau-2)c_\star)\bigr)^{1/(3-\tau)}$ (for the survival half, also at $\tau = 2.5$), for $\rho_1 < \rho_c < \rho_2$: $P^T_{\mathrm{surv}}(\lambda) = 0$ when $T \le \rho_1\lambda^{-1/(3-\tau)}$, and $P^T_{\mathrm{surv}}(\lambda) = \Theta\bigl(\lambda^{(\tau-2)/(3-\tau)}\bigr)$ when $T \ge \rho_2\lambda^{-1/(3-\tau)}$.
2. If $\tau = 2.5$, there are $\rho_1,\rho_2 > 0$ with $P^T_{\mathrm{surv}} = 0$ for $T \le \rho_1\lambda^{-2}$ and $P^T_{\mathrm{surv}} = \Theta(\lambda)$ for $T \ge \rho_2\lambda^{-2}$.
3. If $\tau \in (2.5,3]$, for every $\delta > 0$ there are $\rho_1,\rho_2 > 0$ with $P^T_{\mathrm{surv}} = O\bigl(e^{-\lambda^{-2+\delta}}\bigr)$ for $T \le \rho_1\lambda^{-2}\log(1/\lambda)$, and $P^T_{\mathrm{surv}} = \Theta\bigl(\lambda^{2\tau-4}/\log^{\tau-2}(1/\lambda)\bigr)$ for $T \ge \rho_2\lambda^{-2}\log(1/\lambda)$.
4. If $\tau > 3$, for every $C > 0$ there are $\rho_1,\rho_2 > 0$ with $P^T_{\mathrm{surv}} = O(\lambda^{C})$ for $T \le \rho_1\lambda^{-2}\log^2(1/\lambda)$, and $P^T_{\mathrm{surv}} = \Theta\bigl(\lambda^{2\tau-4}/\log^{2\tau-4}(1/\lambda)\bigr)$ for $T \ge \rho_2\lambda^{-2}\log^2(1/\lambda)$.

So immunising the hubs either leaves the survival probability unchanged up to constants or kills the epidemic (or makes survival negligible), and the switch happens at a maximal degree that is *polynomial* in $1/\lambda$, not the $e^{\Theta(1/\lambda)}$ predicted by mean-field heuristics. Uniform immunisation of a small positive fraction of vertices, in contrast, never prevents survival.

## Expansion

For $\tau \le 2.5$ the threshold is the criticality of the SIR epidemic it dominates: the ever-infected vertices of an SIR infection on a Galton–Watson tree with offspring $D$ form a Galton–Watson tree with mean offspring $\frac{\lambda}{1+\lambda}\mathbb{E}[D]$, and with $D = X\mathbf{1}_{X \le T}$, $T \sim \rho\lambda^{-1/(3-\tau)}$, one has $\mathbb{E}[D] \sim \lambda^{-1}c_\star\frac{\tau-2}{3-\tau}\rho^{3-\tau}$, which crosses $1/\lambda$ exactly at $\rho_c$. For $\tau > 2.5$ survival needs vertices of degree beyond $\lambda^{-2}$: on a star with $k$ leaves the expected extinction time is $e^{\Theta(\lambda^2 k)}$, so such stars hold the infection long enough to pass it to the next large vertex. Upper bounds compare the contact process with a branching random walk with sinks at the large vertices. Since the immunised tree is contained in the truncated tree and the survival strategies never use truncated vertices, both interventions give the same bounds.

## Sources

- John Fernley and Emmanuel Jacob, "Targeted immunization thresholds for the contact process on power-law trees", Stochastic Processes and their Applications 176 (2024), 104425, <https://doi.org/10.1016/j.spa.2024.104425>; numbering as in arXiv:2312.04438: Section 1, main theorem and the claim on immunisation versus truncation; Proposition 4.1.
