# Partner strategies in the noisy alternating game

Consider the strictly alternating donation game (benefit $b$, cost $c$, $b > c > 0$) in which each intended action is flipped with probability $\varepsilon > 0$. Memory-one partner strategies, i.e. Nash equilibria that are fully cooperative in the absence of errors, exist only if

$$\varepsilon < \frac{1}{2}\left(1 - \frac{c}{b}\right),$$

and they are exactly the strategies $q$ with

$$q_{CC} = q_{DC} = 1, \qquad q_{CD} \le 1 - \frac{c}{(1-2\varepsilon)\,b}, \qquad q_{DD} = \frac{(1-2\varepsilon)\,(b + \varepsilon c\, q_{CD}) - c}{(1-2\varepsilon)\,(b + \varepsilon c)} .$$

These conditions describe a line segment in strategy space with endpoints

- Generous Tit-for-Tat, $\mathrm{GTFT} = \left(1,\ 1 - \frac{c}{(1-2\varepsilon)b},\ 1,\ 1 - \frac{c}{(1-2\varepsilon)b}\right)$, and
- Stochastic Firm-but-Fair, $\mathrm{SFBF} = \left(1,\ 0,\ 1,\ \frac{(1-2\varepsilon)b - c}{(1-2\varepsilon)(b + \varepsilon c)}\right)$.

Consequences:

- a partner always reciprocates a co-player's cooperation ($q_{CC} = q_{DC} = 1$) and cooperates with a precisely tuned probability after the co-player defects;
- no deterministic memory-one strategy is a partner, whereas in the simultaneous game Win-Stay Lose-Shift sustains cooperation for $b > 2c$;
- SFBF is the only partner that is deterministic except after mutual defection, and it retaliates against exploitation most strongly ($q_{CD} = 0$);
- every partner can be neutrally invaded by strategies with $q_{CC} = q_{DC} = 1$, such as ALLC and TFT, so cooperation is less robust than in the simultaneous game.

## Depends on

- [Alternating donation game between memory-one players](alternating-game-markov-chain-and-reactive-best-responses.md)
- [Nash equilibria of memory-one strategies in the alternating game](nash-equilibria-of-memory-one-strategies-in-alternating-games.md)

## Proof sketch

With $\varepsilon > 0$ every effective strategy is fully stochastic, so the stationary distribution is unique, and strategies with $q_{CC} = 1$ no longer earn $b - c$ against each other; they differ in how fast they restore cooperation after an error and in how much they gain from the co-player's mistakes. The deviations to ALLC and TFT, automatically neutral without errors, now give binding constraints, and the last condition is exactly the requirement that neither has a selective advantage against $q$; the deviation to ALLD gives the bound on $q_{CD}$. Setting $q_{CD}$ to its upper bound gives GTFT (substituting into the $q_{DD}$ formula returns the same value), and $q_{CD} = 0$ gives SFBF. The SFBF entry $q_{DD}$ is positive exactly when $(1-2\varepsilon)b > c$, which is the error threshold.

## Sources

- P. S. Park, M. A. Nowak, C. Hilbe, "Cooperation in alternating interactions with memory constraints", Nature Communications 13 (2022) 737, Eqs. 5–7 and "Equilibria in alternating games with errors", <https://doi.org/10.1038/s41467-022-28336-2> (PMC8825791).
