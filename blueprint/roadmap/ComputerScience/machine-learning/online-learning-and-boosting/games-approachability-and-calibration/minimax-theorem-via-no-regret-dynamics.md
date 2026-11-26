# Von Neumann's minimax theorem from coupled multiplicative-weights self-play

Let $M : I \times J \to \mathbb{R}$ with $I, J$ finite and nonempty, $\Delta(I)$, $\Delta(J)$ the probability simplices, $N = \max(|I|, |J|)$, and $D = \max M - \min M$. For $T \ge 1$ rounds, the row player plays $p_t \in \Delta(I)$ and the column player plays $q_t \in \Delta(J)$, each by multiplicative weights with the capped rate $\eta = \min\{\sqrt{\ln n/T}, 1/2\}$ ($n = |I|$, respectively $|J|$), where in round $t$ the row player's loss for $i$ is $(\sum_j q_t(j) M(i,j) - \min M)/D$ and the column player's loss for $j$ is $(\max M - \sum_i p_t(i) M(i,j))/D$ (all losses $0$ if $D = 0$). Then the average strategies $\bar p = \frac1T \sum_{t<T} p_t$ and $\bar q = \frac1T \sum_{t<T} q_t$ satisfy

$$
\max_{j \in J} \sum_i \bar p(i) M(i,j) - \min_{i \in I} \sum_j \bar q(j) M(i,j) \le 4D\sqrt{\frac{\ln N}{T}}.
$$

Consequently von Neumann's minimax theorem holds for $M$: $\max_{q \in \Delta(J)} \min_{i \in I} \sum_j q(j) M(i,j) = \min_{p \in \Delta(I)} \max_{j \in J} \sum_i p(i) M(i,j)$, both optima are attained, and $\bar p$, $\bar q$ are optimal up to $4D\sqrt{\ln N/T}$.

## Proof sketch

Write $v_t = \sum_{i,j} p_t(i) q_t(j) M(i,j)$ and $R = 2\sqrt{T \ln N}$. The regret bound of multiplicative weights for losses in $[0,1]$ gives $\sum_t v_t \le \min_i \sum_t \sum_j q_t(j) M(i,j) + D R$ for the row player and $\sum_t v_t \ge \max_j \sum_t \sum_i p_t(i) M(i,j) - D R$ for the column player. Dividing by $T$ and combining, the gap is at most $2D R/T = 4D\sqrt{\ln N/T}$. Since $\min_{i} \sum_j q(j) M(i,j) \le \max_j \sum_i p(i) M(i,j)$ for all $p, q$, the displayed gap bound sandwiches max-min and min-max within $4D\sqrt{\ln N/T}$; let $T \to \infty$, and use compactness of the simplices and continuity for attainment.

## Depends on

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Proof depends on

- [Regret of multiplicative weights: $\eta \sum |\ell| + \ln n/\eta$ and $2\sqrt{T \ln n}$ at every horizon](../regret-in-the-experts-setting/multiplicative-weights-regret-bound.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
- Yoav Freund and Robert E. Schapire, "Adaptive Game Playing Using Multiplicative Weights", Games and Economic Behavior, 1999.
