# Multiplicative weights against best responses solves zero-sum games to accuracy epsilon

Let $M : I \times J \to [0,1]$ be the loss matrix of a zero-sum game (row player pays $M(i,j)$) with value $v$, $n = |I|$, $0 < \varepsilon \le 1$ and $T \ge 4\ln n/\varepsilon^2$. Run multiplicative weights on the rows with rate $\varepsilon/2$, where in round $t$ the column $j_t$ is a best response to the current row distribution $p_t$ and the loss vector is $i \mapsto M(i, j_t)$. Then the average row distribution $\bar p = \frac1T\sum_t p_t$ satisfies $\sum_i \bar p(i) M(i,j) \le v + \varepsilon$ for every column $j$, and the empirical distribution $\bar q$ of $j_0,\ldots,j_{T-1}$ satisfies $\sum_j \bar q(j) M(i,j) \ge v - \varepsilon$ for every row $i$. Moreover the average payoff $\frac1T\sum_t \langle p_t, M(\cdot,j_t)\rangle$ lies in $[v, v+\varepsilon]$.

## Proof sketch

Best responses make each stage payoff at least $v$, so the average payoff is at least $v$. The regret bound against each fixed row with $\eta = \varepsilon/2$ and $T \ge 4\ln n/\varepsilon^2$ shows the average payoff exceeds the loss of every row against $\bar q$ by at most $\varepsilon$, which gives the bound for $\bar q$; best-response optimality of $j_t$ transfers it to $\bar p$.

## Depends on

- [Multiplicative weights (polynomial weights) algorithm](../regret-in-the-experts-setting/polynomial-weights-algorithm.md)
- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Proof depends on

- [Regret of multiplicative weights: $\eta \sum |\ell| + \ln n/\eta$ and $2\sqrt{T \ln n}$ at every horizon](../regret-in-the-experts-setting/multiplicative-weights-regret-bound.md)

## Sources

- Sanjeev Arora, Elad Hazan and Satyen Kale, "The Multiplicative Weights Update Method: a Meta-Algorithm and Applications", Theory of Computing 8, 2012.
- Yoav Freund and Robert E. Schapire, "Adaptive Game Playing Using Multiplicative Weights", Games and Economic Behavior, 1999.
