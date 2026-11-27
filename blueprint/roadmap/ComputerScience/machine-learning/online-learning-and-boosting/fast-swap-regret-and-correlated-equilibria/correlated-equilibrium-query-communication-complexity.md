# Query and communication complexity of approximate correlated equilibria

For normal-form games with a constant number of players and $N$ actions per player and every constant $\varepsilon > 0$: uncoupled no-swap-regret dynamics converge to the set of $\varepsilon$-approximate correlated equilibria within $(\log N)^{O(1/\varepsilon)}$ rounds; the communication complexity of computing an $\varepsilon$-approximate correlated equilibrium is $\log(N)^{\tilde O(1/\varepsilon)}$, which for two players is polylogarithmic in $N$ and resolves an open problem; and the query complexity in the payoff-query model is $N\cdot\log(N)^{\tilde O(1/\varepsilon)} = \tilde O(N)$, giving the first separation between $\varepsilon$-correlated and $\varepsilon$-Nash equilibria in query complexity. For extensive-form games with perfect recall and utilities normalized to $[0,1]$ (so that $\varepsilon$ is an additive error on that scale), an $\varepsilon$-approximate normal-form correlated equilibrium can be computed in time $\mathrm{poly}\big(m, A^\star, (I^\star\log A^\star/\varepsilon)^{1/\varepsilon}\big)$, where $m$ is the number of players, $I^\star$ the largest number of information sets and $A^\star$ the largest number of actions at an information set of any player; this is polynomial in the game tree for every constant $\varepsilon$ (a polynomial-time approximation scheme), although such equilibria were conjectured to be intractable.

## Proof sketch

Each player runs the fast swap-regret algorithm on estimated losses; the empirical distribution of joint play is an approximate correlated equilibrium whose error is the maximum swap regret. Rewards are estimated by sampling the other players' mixed strategies, which costs few payoff queries or few bits per round. For extensive-form games, counterfactual regret minimization supplies an efficient external-regret learner over the exponentially many pure strategies, and the tree reduction turns it into a swap-regret learner of the same per-round cost.

## Depends on

- [Correlated equilibrium](../../../../GameTheory/noncooperative-games/correlated-equilibria/is-correlated-eq.md)
- [Swap regret](../../../../GameTheory/not-yet-classified/part-02/regret/swap-regret.md)

## Proof depends on

- [Swap regret polylogarithmic in the number of actions](polylog-rounds-swap-regret.md)
- [No external regret implies no swap regret, and Littlestone games have correlated equilibria](no-external-regret-implies-no-swap-regret.md)
- [No-swap-regret dynamics converge to correlated equilibria](../../../../GameTheory/noncooperative-games/no-regret-dynamics/no-swap-regret-dynamics-converge-to-correlated-equilibria.md)

## Sources

- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC (2024), arXiv:2310.19647, Corollary 1.3.
- Y. Dagan, C. Daskalakis, M. Fishelson, N. Golowich, "From External to Swap Regret 2.0: An Efficient Reduction for Large Action Spaces", STOC (2024), arXiv:2310.19786, Corollaries 3.7 and 3.9, Theorem 3.11.
