# Nash equilibria of the one-shot transparent anti-coordination game

**Setting.** A one-shot transparent game (each player sees the partner's choice with probability $p_{12}$ for player 1 and $p_{21}$ for player 2, $p_{12} + p_{21} \le 1$; strategies $(s_1; s_2; s_3)$ give the probability of $A_1$ when not seeing, seeing $A_1$, seeing $A_2$) with payoffs $R$ ($A_1$ vs $A_1$), $S$ ($A_1$ vs $A_2$), $T$ ($A_2$ vs $A_1$), $P$ ($A_2$ vs $A_2$). In the anti-coordination game $A_1$ = insist, $A_2$ = accommodate, and $S > T > R > P$.

**Dominance.** Any $(s_1; s_2; s_3)$ is dominated by $(s_1; 0; s_3)$ and by $(s_1; s_2; 1)$: a player who sees the partner act should do the opposite.

**Theorem.** Assume $p_{12} \le p_{21}$. The pure Nash equilibria are:
- player 1 plays $(0;0;1)$, player 2 plays $(1;0;1)$, iff $\dfrac{p_{21}}{1 - p_{12}} \le \dfrac{T - R}{S - R}$ (condition (5));
- player 1 plays $(1;0;1)$, player 2 plays $(0;0;1)$, iff $\dfrac{p_{12}}{1 - p_{21}} \le \dfrac{T - R}{S - R}$ (condition (6));
- both play $(1;0;1)$ iff (6) fails.

Condition (5) implies (6). When (5) holds there is also a mixed equilibrium in which player $i$ plays $(s^i_1; 0; 1)$ with

$$s^1_1 = \frac{(1 - p_{21})(S - P) - p_{12}(T - P)}{(1 - p_{12} - p_{21})(T + S - P - R)}, \qquad s^2_1 = \frac{(1 - p_{12})(S - P) - p_{21}(T - P)}{(1 - p_{12} - p_{21})(T + S - P - R)} .$$

The same classification holds for every one-shot transparent game with $S > T > R$ and $S > P$, which includes Hawk–Dove (Snowdrift) and Leader games.

**Example.** With $(S, T, R, P) = (4, 3, 2, 1)$ and $p_{12} = p_{21} = p$: for $p < 1/3$ there are two asymmetric pure equilibria and a symmetric mixed one with blind insisting probability $(3 - 5p)/(4 - 8p)$; for $p > 1/3$ the unique equilibrium is that both insist unless they see the partner insist.

## Depends on

- [Nash equilibria of the one-shot transparent Prisoner's Dilemma](nash-equilibria-of-the-one-shot-transparent-prisoners-dilemma.md)

## Expansion

Against $(1;0;1)$, player 2's payoff from $(s_1; 0; 1)$ is $T + s_1\big(p_{12}(S - R) + p_{21}(T - R) - (T - R)\big)$ since with probability $p_{12}$ player 1 sees player 2 insist and yields, and with probability $p_{21}$ player 2 sees player 1 insist and yields; so accommodating blindly is a best response exactly under condition (6); this best-response lemma yields the pure equilibria. The mixed equilibrium equalizes the partner's payoffs from insisting and accommodating when unseen. Unlike the simultaneous game, visibility rewards acting first, so in the iterated game fast players can secure the insisting role, which suppresses turn-taking cooperation at high transparency.

## Sources

- A. M. Unakafov, T. Schultze, A. Gail, S. Moeller, I. Kagan, S. Eule, F. Wolf, "Emergence and suppression of cooperation by action visibility in transparent games", PLoS Computational Biology 16(1) (2020) e1007588, Methods: Lemma 5, Lemma 6, Proposition 4 with conditions (5)–(8), Remark 1, Corollary 7 and Proposition 8, <https://doi.org/10.1371/journal.pcbi.1007588>, PMCID: PMC6975562.
