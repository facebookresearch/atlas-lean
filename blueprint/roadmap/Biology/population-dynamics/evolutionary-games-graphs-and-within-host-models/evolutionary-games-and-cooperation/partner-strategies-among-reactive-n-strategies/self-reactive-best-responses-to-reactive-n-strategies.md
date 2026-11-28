# Self-reactive best responses to reactive-n strategies

**Setting.** Two players play the infinitely repeated prisoner's dilemma with simultaneous moves and payoffs $T > R > P > S$, $2R > T + S$; each maximizes the average payoff per round. A player's $n$-history is the tuple $h = (a_{-n}, \dots, a_{-1}) \in \{C, D\}^n$ of its last $n$ actions, and $H = \{C,D\}^n$ has $2^n$ elements.

- A **reactive-$n$ strategy** for player 2 is $p = (p_h)_{h \in H} \in [0,1]^{2^n}$, the probability of cooperating given that player 1's $n$-history is $h$.
- A **self-reactive-$n$ strategy** for player 1 is $\tilde p = (\tilde p_h)_{h \in H}$, the probability of cooperating given player 1's own $n$-history $h$.
- A strategy is **nice** if it is never the first to defect; a nice reactive-$n$ strategy has $p_{C\cdots C} = 1$. A **partner** is a nice strategy that is a Nash equilibrium.

**Theorem.** Let player 2 use a reactive-$n$ strategy $p$.

1. For every strategy $\sigma$ of player 1, of arbitrary memory, there is a self-reactive-$n$ strategy $\tilde p$ that yields the same payoffs for both players against $p$.
2. Against $p$ a best response can be found among the $2^{2^n}$ deterministic self-reactive-$n$ strategies.

**Corollary (partner test).** A nice reactive-$n$ strategy $p$ is a partner if and only if $\pi_1(\tilde p, p) \le R$ for every deterministic self-reactive-$n$ strategy $\tilde p$. A deterministic self-reactive strategy ignores the co-player and produces an eventually periodic action sequence, so the test reduces to finitely many periodic sequences. In the donation game ($R = b - c$, $S = -c$, $T = b$, $P = 0$), a sequence of period $m$ containing $d$ defections earns $b$ times the sum of $p$'s cooperation probabilities over the $m$ histories it presents, minus $(m - d)\,c$, per period, so the test reads

$$\frac{1}{m}\sum_{t=1}^{m} p_{h_t} \le 1 - \frac{d}{m}\cdot\frac{c}{b}$$

for every periodic sequence, where $h_1, \dots, h_m$ are the $n$-histories it presents. For $n = 1$ this recovers the classical reactive partners $p_C = 1$, $p_D \le 1 - c/b$ (Generous Tit-for-Tat and its less generous variants).

## Proof depends on

- [Average-reward optimality equation](../../../../../ComputerScience/heuristic-search-and-planning/markov-decision-processes/average-reward-optimality-equation.md)

## Proof sketch

Part 1 follows the intuition of the Press–Dyson argument: player 2 reacts only to player 1's last $n$ actions, so any part of the joint history that player 2 ignores cannot help player 1. Averaging player 1's conditional cooperation probabilities over that unused information, with stationary weights, gives a self-reactive-$n$ strategy with the same long-run distribution of outcomes. For part 2, player 1's problem against $p$ becomes a Markov decision problem on player 1's own $n$-histories, and average-reward problems of this kind admit deterministic stationary optimal policies. For the donation game, the payoff of a periodic sequence is additive across rounds: in a round where the sequence player's last $n$ actions are $h$, it receives $b$ with probability $p_h$ and pays $c$ if it cooperates. Comparing with the per-round partner payoff $b - c$ gives the displayed inequality; for example the alternating sequence $DC$ presents the histories $CD$ and $DC$ for $n = 2$ and yields $(p_{CD} + p_{DC})/2 \le 1 - c/(2b)$.

## Sources

- N. E. Glynatsi, E. Akin, M. A. Nowak, C. Hilbe, "Conditional cooperation with longer memory", Proceedings of the National Academy of Sciences USA 121(50) (2024) e2420125121, "An Algorithm to Identify Partners Among Reactive-n Strategies", Fig. 3, and Materials and Methods, <https://doi.org/10.1073/pnas.2420125121> (PMC11648855).
