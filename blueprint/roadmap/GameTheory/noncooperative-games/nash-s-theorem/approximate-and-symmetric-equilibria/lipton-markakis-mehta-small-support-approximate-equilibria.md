# Lipton–Markakis–Mehta small-support approximate equilibria

Let $(A, B)$ be a bimatrix game with nonempty finite strategy sets $M, N$ and all payoffs in $[0, 1]$, and let $\varepsilon > 0$. For every integer

$$
k > \frac{2 \ln\bigl(2(|M| + |N|)\bigr)}{\varepsilon^2}
$$

there are multisets $m_1$ of rows and $m_2$ of columns, each of size $k$, such that the uniform distributions on $m_1$ and $m_2$ form an $\varepsilon$-approximate Nash equilibrium. If payoffs lie in $[0, K]$ instead, the same multisets give a $K\varepsilon$-approximate equilibrium.

## Proof sketch

Take an exact Nash equilibrium and sample $k$ pure strategies independently from each mixed strategy. By Hoeffding's inequality each of the $|M| + |N|$ deviation payoffs is estimated to within $\varepsilon/2$ except with probability below $1/(|M| + |N|)$; a union bound leaves positive probability that all are accurate, which yields the approximate equilibrium.

## Depends on

- [Additive approximate Nash equilibrium](additive-approximate-nash-equilibrium.md)

## Proof depends on

- [Nash's theorem](../exists-is-mixed-nash.md)
- [Chernoff bound for the empirical mean of real-valued i.i.d. variables](../../../../Probability/large-deviations/cram-r-s-theorem/measure-empirical-mean-le-of-threshold.md)

## Sources

- Richard J. Lipton, Evangelos Markakis and Aranyak Mehta, "Playing Large Games Using Simple Strategies", Proceedings of the 4th ACM Conference on Electronic Commerce (EC 2003), 2003.
- Eva Tardos and Vijay V. Vazirani, "Basic Solution Concepts and Computational Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
