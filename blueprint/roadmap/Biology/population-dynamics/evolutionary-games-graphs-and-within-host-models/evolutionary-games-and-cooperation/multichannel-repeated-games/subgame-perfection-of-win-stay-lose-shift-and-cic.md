# Subgame perfection of Win-Stay Lose-Shift and of CIC in multichannel games

In the same multichannel donation game with $m$ parallel games of benefits $b_k$ and costs $c_k$, consider two memory-one strategies. **Win-Stay Lose-Shift (WSLS)** is unlinked: in each game a player cooperates if both players made the same choice in that game in the previous round (both cooperated or both defected), and defects otherwise; equivalently, it keeps its previous action after a payoff of $b_k - c_k$ or $b_k$ in that game and switches after $0$ or $-c_k$. **CIC** is linked: a player uses the *same* action in all games in a round, cooperating if and only if in each game the two players used the same action in the previous round, and defecting otherwise. Then

- WSLS is a subgame perfect equilibrium **iff** $b_k \ge 2 c_k$ for every game $k$;
- CIC is a subgame perfect equilibrium **iff** $\displaystyle \sum_{k=1}^{m} b_k \;\ge\; 2 \sum_{k=1}^{m} c_k$.

The unlinked condition must hold in every single game; the linked condition only on average, so cooperation in a high-benefit game with $b_k > 2c_k$ can carry a low-benefit game with $b_k < 2 c_k$.

## Depends on

- [Partner strategies in linked multichannel donation games](partner-strategies-in-linked-multichannel-donation-games.md)

## Remarks

Subgame perfection is stronger than Nash: no player may gain by deviating after *any* history of play, which rules out equilibria sustained by threats that would not be carried out. Both conditions come from comparing the continuation payoff of following the strategy with that of a one-shot deviation after an arbitrary history; the $2c_k$ threshold is the usual WSLS condition in a single repeated donation game, where a deviation from mutual cooperation earns $b_k$ once and is followed by one round of mutual defection before cooperation resumes, so it forgoes two rounds of $b_k - c_k$ and pays exactly when $b_k > 2(b_k - c_k)$, that is $b_k < 2c_k$. The averaging in the CIC condition is the same structural effect as in the characterization of linked partner strategies: a linked strategy punishes across channels, so the incentive constraint is pooled over the channels rather than imposed on each. Simulations with memory-one strategies agree: unlinked populations sustain little cooperation in games with $b_k < 2c_k$, while linked populations converge on CIC-like behaviour and cooperate in both.

## Sources

- K. Donahue, O. P. Hauser, M. A. Nowak, C. Hilbe, "Evolving cooperation in multichannel games", *Nature Communications* 11 (2020), 3885, <https://doi.org/10.1038/s41467-020-17730-3> (PMC7403149). Proposition 5 ("Stability of WSLS and CIC"), Supplementary Note 4, restated in Methods, "Analytical results for memory-1 strategies".
