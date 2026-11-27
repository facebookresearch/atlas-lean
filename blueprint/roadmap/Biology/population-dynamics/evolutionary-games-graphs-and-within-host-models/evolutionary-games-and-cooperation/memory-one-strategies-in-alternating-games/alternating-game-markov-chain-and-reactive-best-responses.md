# Alternating donation game between memory-one players

**Game.** Two players repeatedly choose cooperate ($C$) or defect ($D$) in a strictly alternating order: player 1 moves, then player 2 moves knowing player 1's move, and so on. Payoffs attach to individual actions as in the donation game: cooperating costs $c > 0$ and gives the co-player $b > c$ (equivalently $R = b - c$, $S = -c$, $T = b$, $P = 0$). The game is infinitely repeated without discounting.

**Strategies.** A memory-one strategy is $p = (p_{CC}, p_{CD}, p_{DC}, p_{DD}) \in [0,1]^4$, where $p_{ij}$ is the probability of cooperating when the player's own last move was $i$ and the co-player's last move was $j$. It is reactive if $p_{CC} = p_{DC}$ and $p_{CD} = p_{DD}$ (only the co-player's move matters), and deterministic if every entry is $0$ or $1$. With implementation errors at rate $\varepsilon$ the effective strategy is $p_\varepsilon = (1-\varepsilon)p + \varepsilon(1-p)$.

**Payoffs.** If player 1 uses $p$ and player 2 uses $q$, the pair of most recent moves $(a_1, a_2) \in \{CC, CD, DC, DD\}$ is a Markov chain with transition matrix

$$M_A = \begin{pmatrix}
p_{CC}q_{CC} & p_{CC}(1-q_{CC}) & (1-p_{CC})q_{CD} & (1-p_{CC})(1-q_{CD}) \\
p_{CD}q_{DC} & p_{CD}(1-q_{DC}) & (1-p_{CD})q_{DD} & (1-p_{CD})(1-q_{DD}) \\
p_{DC}q_{CC} & p_{DC}(1-q_{CC}) & (1-p_{DC})q_{CD} & (1-p_{DC})(1-q_{CD}) \\
p_{DD}q_{DC} & p_{DD}(1-q_{DC}) & (1-p_{DD})q_{DD} & (1-p_{DD})(1-q_{DD})
\end{pmatrix}:$$

player 1 reacts to the previous pair, and player 2 then reacts to its own previous move and to player 1's new move. For a stationary distribution $v = v M_A$ with $v = (v_{CC}, v_{CD}, v_{DC}, v_{DD})$, the long-run payoffs are

$$\pi_1 = (v_{CC} + v_{DC})\,b - (v_{CC} + v_{CD})\,c, \qquad \pi_2 = (v_{CC} + v_{CD})\,b - (v_{CC} + v_{DC})\,c .$$

The stationary distribution is unique when both strategies are fully stochastic or $\varepsilon > 0$; otherwise the first moves must be specified.

**Reduction of best responses.** Let $q$ be a memory-one strategy.

1. For every memory-one $p$ there is a reactive $\tilde p$ that yields the same stationary distribution, hence the same payoff, against $q$.
2. Among reactive strategies, a best response to $q$ can be chosen deterministic.

Hence $q$ is a Nash equilibrium ($\pi(q,q) \ge \pi(p,q)$ for all memory-one $p$) if and only if $\pi(q,q)$ is at least the payoff against $q$ of each of the four deterministic reactive strategies ALLD $=(0,0,0,0)$, ALLC $=(1,1,1,1)$, TFT $=(1,0,1,0)$ and ATFT $=(0,1,0,1)$. In the alternating game a player can thus afford to remember strictly less than the opponent: the co-player's last move suffices for a best response.

## Proof depends on

- [Existence of a stationary distribution](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/exists-stationary.md)
- [Uniqueness of the stationary distribution of a primitive chain](../../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/stationary-unique.md)

## Proof sketch

In the alternating game player 2's move in a round depends on player 1's move in that same round, while player 1's move depends on the pair from the previous round. With $q$ fixed, player 1's own last move influences the future only through player 1's own choice, so player 1 can replace $p$ by a reactive strategy that cooperates, after each co-player move $j$, with the stationary-weighted average of $p_{Cj}$ and $p_{Dj}$; this leaves the outcome distribution unchanged. Supplementary Note 2 of the paper then shows that, within the two-dimensional set of reactive strategies, a best response can be taken at one of the four vertices, the deterministic reactive strategies. This parallels the Press–Dyson observation for the simultaneous game that remembering more than the opponent gives no advantage. The simultaneous game uses a different matrix $M_S$, in which both players react to the same previous pair.

## Sources

- P. S. Park, M. A. Nowak, C. Hilbe, "Cooperation in alternating interactions with memory constraints", Nature Communications 13 (2022) 737, Model description, "A recipe for identifying Nash equilibria for alternating games", and Methods Eqs. 8–9, <https://doi.org/10.1038/s41467-022-28336-2> (PMC8825791).
