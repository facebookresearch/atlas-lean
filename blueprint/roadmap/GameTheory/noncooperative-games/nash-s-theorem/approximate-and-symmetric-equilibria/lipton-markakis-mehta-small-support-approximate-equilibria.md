# Lipton–Markakis–Mehta small-support approximate equilibria

Let $(A, B)$ be an $n \times n$ bimatrix game with all payoffs in $[0, 1]$, let $(x^*, y^*)$ be a Nash equilibrium of it, and let $\varepsilon > 0$. For every integer

$$
k \ge \frac{12 \ln n}{\varepsilon^2}
$$

there are multisets $m_1$ of rows and $m_2$ of columns, each of size $k$, such that the uniform distributions on $m_1$ and $m_2$ form an $\varepsilon$-approximate Nash equilibrium.

## Proof sketch

Sample $k$ pure strategies independently from $x^*$ and from $y^*$. By Hoeffding's inequality each of the $2n$ pure-deviation payoffs against the sampled opponent strategy lies within $\varepsilon/2$ of its value at $(x^*, y^*)$ except with probability at most $2e^{-k\varepsilon^2/2} \le 2n^{-6}$, and a union bound leaves positive probability that all of them are accurate when $n \ge 2$ (the case $n = 1$ is trivial). Every sampled row and column lies in the support of the equilibrium and is a best response there, so the sampled pair is then an $\varepsilon$-approximate equilibrium.

## Depends on

- [Additive approximate Nash equilibrium](additive-approximate-nash-equilibrium.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Proof depends on

- [Chernoff bound for the empirical mean of real-valued i.i.d. variables](../../../../Probability/large-deviations/cram-r-s-theorem/measure-empirical-mean-le-of-threshold.md)

## Sources

- Richard J. Lipton, Evangelos Markakis and Aranyak Mehta, "Playing Large Games Using Simple Strategies", Proceedings of the 4th ACM Conference on Electronic Commerce (EC 2003), 2003, Theorem 1 (for every Nash equilibrium of an $n \times n$ game with payoffs in $[0, 1]$ and every $k \ge 12 \ln n/\varepsilon^2$ there is a pair of $k$-uniform strategies forming an $\varepsilon$-Nash equilibrium).
- Eva Tardos and Vijay V. Vazirani, "Basic Solution Concepts and Computational Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
