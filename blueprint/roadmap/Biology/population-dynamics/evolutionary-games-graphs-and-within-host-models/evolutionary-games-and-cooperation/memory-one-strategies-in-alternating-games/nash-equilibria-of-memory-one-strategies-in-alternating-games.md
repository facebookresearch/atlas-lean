# Nash equilibria of memory-one strategies in the alternating game

In the infinitely repeated, strictly alternating donation game without errors (benefit $b$, cost $c$, $b > c > 0$), a memory-one strategy $q = (q_{CC}, q_{CD}, q_{DC}, q_{DD})$ is a Nash equilibrium if and only if it belongs to one of three classes.

- **Partners** (fully cooperative against themselves, and Nash):

$$q_{CC} = 1, \qquad q_{CD} \le 1 - \frac{c}{b-c}\,q_{DD}, \qquad q_{CD} \le 1 - \frac{c}{b}\,q_{DC}.$$

If one of the two inequalities fails, $q$ can be invaded by ALLD or by Anti-Tit-for-Tat.
- **Defectors** (mutual defection against themselves, and Nash):

$$q_{DD} = 0, \qquad q_{DC} \le \frac{c}{b}\,(1 - q_{CD}), \qquad q_{DC} \le \frac{c}{b-c}\,(1 - q_{CC}).$$

- **Equalizers** (strategies that fix the co-player's payoff whatever the co-player does):

$$q_{CD} = \frac{b\,q_{CC} - c\,(1 + q_{DD})}{b - c}, \qquad q_{DC} = \frac{b\,q_{DD} + c\,(1 - q_{CC})}{b - c}.$$

Partners and defectors each form a three-dimensional polyhedron. The partner polyhedron grows with $b/c$, never contains ALLC, always contains TFT and GRIM (with cooperation in the first round), and contains Win-Stay Lose-Shift $(1,0,0,1)$ and Firm-but-Fair $(1,0,1,1)$ when $b \ge 2c$. The defector polyhedron is never empty and always contains ALLD. The algebraic conditions coincide with those for the simultaneous repeated donation game, but the simultaneous game has a fourth class, the alternators, which cooperate in one round and defect in the next; such behavior cannot arise among memory-one players in the alternating game.

## Depends on

- [Alternating donation game between memory-one players](alternating-game-markov-chain-and-reactive-best-responses.md)
- [X sets Y's score: equalizer strategies](../../../zero-determinant-strategies-in-iterated-games/equalizer-score.md)

## Proof sketch

By the reduction to deterministic reactive deviations, $q$ is Nash iff $\pi(q,q) \ge \pi(s,q)$ for $s \in \{\mathrm{ALLD}, \mathrm{ALLC}, \mathrm{TFT}, \mathrm{ATFT}\}$. For $q_{CC} = 1$ the self-payoff is $b - c$, and ALLC and TFT also earn $b - c$ against such a strategy, so only ALLD and ATFT constrain $q$; their stationary payoffs against $q$, computed from the alternating transition matrix, give the two linear inequalities. The defector conditions arise in the same way with self-payoff $0$. The converse (there are no other equilibria) is proved in the paper's Supplementary Note 2, with a proof that is simpler than the existing one for the simultaneous game. Example: for WSLS the first partner inequality reads $0 \le 1 - c/(b-c)$, i.e. $b \ge 2c$, and the second holds trivially.

## Sources

- P. S. Park, M. A. Nowak, C. Hilbe, "Cooperation in alternating interactions with memory constraints", Nature Communications 13 (2022) 737, Eqs. 2–4 and "Equilibria in alternating games without errors", <https://doi.org/10.1038/s41467-022-28336-2> (PMC8825791).
