# Pull-count bound for UCB1

Let UCB1 run on $K \ge 2$ arms with independent rewards supported in $[0,1]$, playing each arm once and
then an arm maximizing $\bar x_j + \sqrt{2 \ln t / n_j}$, where $t$ is the number of plays made so far and
$n_j$ the number of plays of arm $j$. For every arm $i$ with gap
$\Delta_i > 0$ and every $n \ge K$,

$$\mathbb{E}[T_i(n)] \le \frac{8 \ln n}{\Delta_i^2} + 1 + \frac{\pi^2}{3}.$$

## Related topics

- [Anytime regret bound for UCB1](anytime-regret-bound-for-ucb1.md)

## Sources

- P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis of the multiarmed bandit problem*, Machine Learning 47 (2002) 235–256, Figure 1 and the proof of Theorem 1, which bounds $\mathbb{E}[T_i(n)]$ by $\lceil 8 \ln n / \Delta_i^2 \rceil + \pi^2/3$. <https://homes.di.unimi.it/~cesa-bianchi/Pubblicazioni/ml-02.pdf>
