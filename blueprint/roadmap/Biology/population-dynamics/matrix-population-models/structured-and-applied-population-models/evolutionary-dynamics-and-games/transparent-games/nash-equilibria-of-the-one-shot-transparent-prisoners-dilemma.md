# Nash equilibria of the one-shot transparent Prisoner's Dilemma

**Transparent game.** Two players choose between actions $A_1$ and $A_2$ in continuous time, so each may see the partner's choice before committing: player $i$ sees the partner's action with probability $p_i$, and $p_1 + p_2 \le 1$ (with probability $1 - p_1 - p_2$ neither sees). A strategy is $s = (s_1; s_2; s_3)$: the probability of $A_1$ when not seeing, when seeing the partner choose $A_1$, and when seeing the partner choose $A_2$. With payoffs $R$ ($A_1$ vs $A_1$), $S$ ($A_1$ vs $A_2$), $T$ ($A_2$ vs $A_1$), $P$ ($A_2$ vs $A_2$), player 1's expected payoff against $s'$ is

$$E(s, s') = (1 - p_1 - p_2)\,u(s_1, s'_1) + p_2\big(s_1(s'_2R + (1-s'_2)S) + (1-s_1)(s'_3T + (1-s'_3)P)\big) + p_1\big(s'_1(s_2R + (1-s_2)T) + (1-s'_1)(s_3S + (1-s_3)P)\big),$$

where $u(a,b) = abR + a(1-b)S + (1-a)bT + (1-a)(1-b)P$.

**Prisoner's Dilemma** ($A_1$ = cooperate, $T > R > P > S$), equal visibility $p_1 = p_2 = p \in (0, 1/2]$.

- *Dominance.* Any $(s_1; s_2; s_3)$ is dominated by $(s_1; 0; s_3)$ and by $(s_1; s_2; 0)$: cooperating after seeing the partner's choice never pays.
- *Equilibria.* The Nash equilibria are exactly the pairs $(0; x; 0)$, $(0; y; 0)$ with

$$0 \le x, y \le \frac{1-p}{p}\,\frac{P - S}{R - S}.$$

All equilibria are mutual defection, but unconditional defection $(0;0;0)$ is not evolutionarily stable, because the neutral variants $(0; x; 0)$ earn the same payoff.
- *Defectors versus blind cooperators.* For $(1;0;0)$ against $(0;x;0)$: if $x$ satisfies the equilibrium bound and $x \le \frac{1}{p} - 2 + \frac{P - S}{T - R}$, then $(0;x;0)$ dominates; if neither holds, $(1;0;0)$ dominates; if only the first holds, they coexist; if only the second, they are bistable.
- *Unequal reaction times.* Pure cooperators $(1;0;0)$ that see defectors with probability $p_{12}$ (seeing one another with probability $p_{11} \le 1/2$), and are seen by defectors with probability $p_{21}$, where $0 < p_{21} < p_{12} < 1$, and pure defectors $(0;0;0)$ are bistable iff $p_{12} > \frac{T-R}{T-P} + \frac{2R - S - T}{T - P}\,p_{11}$; for $(T,R,P,S) = (5,3,1,0)$ this reads $p_{12} > \tfrac12 + \tfrac14 p_{11}$, so cooperators can resist invasion when they see defections with probability above $5/8$.

## Expansion

$E$ is affine in each strategy entry, so best responses are found entrywise. Against any partner, replacing $s_2 > 0$ by $0$ changes the payoff by $p\,s'_1 s_2(T - R) \ge 0$ and replacing $s_3 > 0$ by $0$ gains through $P > S$, giving the dominance lemma. Against $(0; x; 0)$ the payoff of $(s_1; 0; 0)$ is $P + s_1\,p(R - S)\big(x - \frac{1-p}{p}\frac{P-S}{R-S}\big)$, so defecting is a best response iff the bound holds, and any other candidate equilibrium can be improved by switching to unconditional defection. In evolutionary simulations of the iterated game, visibility creates the neutral drift $(0;0;0) \leftrightarrow (0;x;0)$ that opens a path back towards cooperation.

## Sources

- A. M. Unakafov, T. Schultze, A. Gail, S. Moeller, I. Kagan, S. Eule, F. Wolf, "Emergence and suppression of cooperation by action visibility in transparent games", PLoS Computational Biology 16(1) (2020) e1007588, Methods: equation (1), Definitions 1–2, Lemma 1, Propositions 2–3 with conditions (2)–(4), <https://doi.org/10.1371/journal.pcbi.1007588>, PMCID: PMC6975562.
