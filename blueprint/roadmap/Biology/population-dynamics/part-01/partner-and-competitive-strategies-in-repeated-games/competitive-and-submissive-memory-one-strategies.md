# Competitive and submissive memory-one strategies

**Setting.** As in
[memory-one partner strategies in the iterated prisoner's dilemma](memory-one-partner-strategies-in-the-iterated-prisoners-dilemma.md):
payoffs $T > R > P > S$, discount factor $\delta < 1$, memory-one strategies
$p = (p_{CC}, p_{CD}, p_{DC}, p_{DD}; p_0)$ and mean outcome distribution $v$ with
$\pi_I - \pi_{II} = (T - S)(v_{DC} - v_{CD})$.

**Definitions.** A strategy for player I is **competitive** if $\pi_I \ge \pi_{II}$ against every
co-player, and **submissive** if $\pi_I \le \pi_{II}$ against every co-player.

**Proposition (competitive).** For a memory-one strategy $p$ the following are equivalent:

1. $p$ is competitive;
2. $\pi_I \ge \pi_{II}$ against AllD $= (0, 0, 0, 0; 0)$ and against $(0, 0, 0, 1; 0)$;
3. $p_0 = p_{DD} = 0$ and $\delta (p_{CD} + p_{DC}) \le 1$.

**Proposition (submissive).** For a memory-one strategy $p$ the following are equivalent:

1. $p$ is submissive;
2. $\pi_I \le \pi_{II}$ against AllC $= (1, 1, 1, 1; 1)$ and against $(0, 1, 1, 1; 1)$;
3. $p_0 = p_{CC} = 1$ and $\delta (1 - p_{CD}) + \delta (1 - p_{DC}) \le 1$.

In particular every competitive strategy is cautious (never first to cooperate) and every submissive
strategy is nice; AllD and Tit-for-Tat with $p_0 = 0$ are competitive.

## Depends on

- [Memory-one partner strategies in the iterated prisoner's dilemma](memory-one-partner-strategies-in-the-iterated-prisoners-dilemma.md)

## Expansion

Against AllD, $\pi_I - \pi_{II} = -(T - S)\frac{(1 - \delta) p_0 + \delta p_{DD}}{1 + \delta (p_{DD} - p_{CD})}$, forcing
$p_0 = p_{DD} = 0$; against $(0, 0, 0, 1; 0)$ the difference has the sign of $1 - \delta(p_{CD} + p_{DC})$.
Conversely, with $p_0 = p_{DD} = 0$ the memory-one identity reads
$\delta p_{DC} v_{DC} = (1 - \delta p_{CC}) v_{CC} + (1 - \delta p_{CD}) v_{CD}$, and
$\delta p_{DC} \le 1 - \delta p_{CD}$ gives $(1 - \delta p_{CD})(v_{DC} - v_{CD}) \ge (1 - \delta p_{CC}) v_{CC} \ge 0$,
so $v_{DC} \ge v_{CD}$. The submissive case is the mirror image under exchanging $C$ and $D$. Partners
secure $R$ without trying to win each encounter; rivals never lose an encounter but cannot sustain
cooperation with themselves, which is the trade-off behind the evolutionary success of each class.

## Sources

- C. Hilbe, A. Traulsen, K. Sigmund, "Partners or rivals? Strategies for the iterated prisoner's
  dilemma", Games and Economic Behavior 92 (2015), Definition 3 and Propositions 2-3,
  <https://doi.org/10.1016/j.geb.2015.05.005> (PMC4547490).
