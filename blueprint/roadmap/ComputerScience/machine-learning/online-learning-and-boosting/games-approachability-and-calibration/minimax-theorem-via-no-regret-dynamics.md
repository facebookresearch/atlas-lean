# Von Neumann's minimax theorem from coupled multiplicative-weights self-play

For every finite real matrix $M : I \times J \to \mathbb{R}$, with $\Delta(I), \Delta(J)$ the probability simplices,

$$
\max_{q \in \Delta(J)} \min_{i \in I} \sum_j q(j) M(i,j) = \min_{p \in \Delta(I)} \max_{j \in J} \sum_i p(i) M(i,j),
$$

and the common value is attained. Quantitatively, if two multiplicative-weights learners play against each other for $T$ rounds on $M$ rescaled affinely into $[0,1]$, the gap between the two sides is $O(1/\sqrt{T})$ (times the range of $M$), which tends to $0$.

## Proof sketch

The inequality max-min $\le$ min-max is elementary. For the reverse, run both players with multiplicative weights; the average row strategy pays at most the average loss plus $R/T$ against every column, and the average column strategy collects at least the average loss minus $R/T$ against every row. Hence min-max $\le$ max-min $+ 2R/T$ with $R = 2\sqrt{T\ln\max(|I|,|J|)}$; let $T \to \infty$ and use compactness of the simplices for attainment.

## Depends on

- [Von Neumann's minimax theorem](../../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md)

## Proof depends on

- [Regret of multiplicative weights: $\eta \sum |\ell| + \ln n/\eta$ and $2\sqrt{T \ln n}$ at every horizon](../regret-in-the-experts-setting/multiplicative-weights-regret-bound.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
- Yoav Freund and Robert E. Schapire, "Adaptive Game Playing Using Multiplicative Weights", Games and Economic Behavior, 1999.
