# Number of equilibria of replicator–mutator social dilemmas with a random temptation payoff

**Model.** Two strategies, cooperate ($S_1$, frequency $x$) and defect ($S_2$), play a pairwise game with payoffs $R = 1$ (mutual cooperation), $P = 0$ (mutual defection), sucker's payoff $S \in [-1,1]$ and temptation $T \in [0,2]$. Under the replicator–mutator equation $\dot x_i = \sum_j x_j f_j(\mathbf{x})q_{ji} - x_i\bar f(\mathbf{x})$ with symmetric mutation probability $q \in (0, \frac12)$, the equilibria are the roots in $[0,1]$ of

$$(T + S - 1)x^3 + \big(1 - T - 2S + q(S - 1 - T)\big)x^2 + \big(S + q(T - S)\big)x = 0,$$

so $x = 0$ is always an equilibrium and the others are roots of the quadratic $h(x) = ax^2 + bx + c$ with $a = T + S - 1$, $b = 1 - T - 2S + q(S - 1 - T)$, $c = S + q(T - S)$. The four dilemmas are Prisoner's Dilemma (PD: $T > 1 > 0 > S$), Snow-Drift (SD: $T > 1 > S > 0$), Stag Hunt (SH: $1 > T > 0 > S$) and Harmony (H: $1 > T$, $S > 0$). Define

$$s_1 = \frac{-q(1-q)}{1-2q}, \quad s_2 = \frac{q}{q-1}, \quad T_3 = \frac{(q-1)S}{q}, \quad T_{1,2} = \frac{-\big((1-q)qS + q^2 + 2q - 1\big) \mp 2\sqrt{2q^3 - q^2 - (2q^3 - 3q^2 + q)S}}{(1-q)^2}.$$

**Theorem.** Let $T \sim \mathcal{N}(T_0, \sigma^2)$ with $S$ fixed, $T_0$ and $S$ respecting the ordering of the game. Then the probability $p_k$ that the dynamics has exactly $k$ equilibria is:
- for every game, $p_2 = \frac12 - \frac12\,\mathrm{erf}\!\Big(\frac{T_3 - T_0}{\sigma\sqrt2}\Big)$;
- for SD and H games, $p_3 = 1 - p_2$ and $p_1 = 0$, and $p_2 \ge \frac12 - \frac12\,\mathrm{erf}\big(-\frac{S + T_0}{\sigma\sqrt2}\big) > \frac12$;
- for PD and SH games, $p_1 = 1 - p_2 - p_3$ with

$$p_3 = \begin{cases}\frac12\Big[1 + \mathrm{erf}\Big(\frac{T_1 - T_0}{\sigma\sqrt2}\Big)\Big], & S \le s_1,\\[4pt] \frac12\Big[1 + \mathrm{erf}\Big(\frac{T_1 - T_0}{\sigma\sqrt2}\Big) + \mathrm{erf}\Big(\frac{T_3 - T_0}{\sigma\sqrt2}\Big) - \mathrm{erf}\Big(\frac{T_2 - T_0}{\sigma\sqrt2}\Big)\Big], & s_1 < S < s_2,\\[4pt] \frac12\Big[1 + \mathrm{erf}\Big(\frac{T_3 - T_0}{\sigma\sqrt2}\Big)\Big], & S \ge s_2.\end{cases}$$

As a function of the mutation rate $q$, $p_2$ decreases in SD and H games and increases in PD and SH games, with $\lim_{q\to0}p_2 = 1$ for SD and H and $0$ for PD and SH. An analogous classification holds when $S \sim \mathcal{N}(S_0, \sigma^2)$ is random and $T = T_0$ fixed, with thresholds $S_{1,2} = \frac{(q-1)(T_0+1) \mp 2\sqrt{T_0 - 2qT_0}}{q}$; there $p_2$ increases in $q$ in all four games.

## Proof sketch

Writing $t = x/(1-x)$ turns the interior equilibrium condition into a quadratic in $t \in (0,\infty)$, so the number of equilibria is one more than the number of positive roots, decided by the sign of the discriminant $\Delta$ and of the root sum and product. As functions of $T$ these signs change exactly at $T_1, T_2$ (where $\Delta = 0$) and $T_3$ (where $c = 0$, so a root crosses $x = 0$), which partitions the $T$-axis into intervals with $1$, $2$ or $3$ equilibria; integrating the Gaussian density over them gives the error-function formulas. Without mutation, SH and SD always have an interior equilibrium $S/(S+T-1)$; mutation shifts and can destroy it, which is how uncertainty in payoffs and mutation together control behavioural diversity.

## Sources

- Luoer Chen, Churou Deng, Manh Hong Duong and The Anh Han, "On the number of equilibria of the replicator-mutator dynamics for noisy social dilemmas", *Chaos, Solitons & Fractals* 180 (2024), 114565, <https://doi.org/10.1016/j.chaos.2024.114565>. Preprint version: arXiv:2303.16558 (2023), model and game parameterization (Section 2), Theorems 1 and 2 (Section 2.3), equilibrium analysis and thresholds (Section 3.1), Lemmas 1 and 2, <https://doi.org/10.48550/arXiv.2303.16558>.
