# Average loss of an external-regret learner in a matrix game is at most value plus R/T

Let $M : I \times J \to \mathbb{R}$ be a finite matrix game with minimax value $v$ (row player minimizing). Let $q_0, \ldots, q_{T-1}$ be arbitrary mixed column strategies, $T > 0$, and let the row learner's distributions $p_t$ have external regret at most $R$ against the stage loss vectors $i \mapsto \sum_j q_t(j) M(i,j)$. Then

$$
\frac{1}{T}\sum_{t<T} \sum_{i,j} p_t(i)\, q_t(j)\, M(i,j) \le v + \frac{R}{T}.
$$

In a constant-sum game $s_1 + s_2 \equiv c$ in which $s_1$ has value $v_1$, player 2's transposed loss matrix has value $c - v_1$; a column learner with regret $R$ has average loss at most $(c - v_1) + R/T$, and if both players have external regrets $R_1, R_2$, player 1's average loss lies in $[v_1 - R_2/T,\ v_1 + R_1/T]$.

## Proof sketch

Let $\bar q$ be the average of the column strategies. The regret bound compares the learner's total loss with the best fixed row against $\bar q$, which is $T \min_i \sum_j \bar q(j)M(i,j) \le T v$ by the minimax theorem. The constant-sum statements follow by applying this to each player and using $s_2 = c - s_1$.

## Depends on

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)
- [External regret](../../../../GameTheory/noncooperative-games/external-and-swap-regret/external-regret.md)

## Proof depends on

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
