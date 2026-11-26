# Gumbel-type limit of the slowest first passage times

Let $\tau_1, \tau_2, \dots$ be independent copies of a random variable $\tau > 0$ (the first passage time of one searcher to a target) with survival probability $S(t) = \mathbb P(\tau > t)$. For $N \ge 1$ let $T_{1,N} \le \dots \le T_{N,N}$ be the order statistics of $\tau_1, \dots, \tau_N$, so that $T_{N,N}$ is the slowest first passage time and $T_{N-k,N}$ the $(k+1)$-st slowest. Exactly,

$$\mathbb P(T_{N-k,N} \le t) = \sum_{i=0}^{k} \binom{N}{i} (1 - S(t))^{N-i} S(t)^i .$$

**Theorem.** Assume $S(t) \sim A (\lambda t)^{-p} e^{-\lambda t}$ as $t \to \infty$ for some $A > 0$, $\lambda > 0$ and $p \in \mathbb R$. Let $(b_N)$ be any sequence with $b_N - b_N^0 \to 0$, where

$$b_N^0 = \begin{cases} \ln(AN), & p = 0, \\ p\, W_0\bigl(\tfrac1p (AN)^{1/p}\bigr), & p > 0, \\ p\, W_{-1}\bigl(\tfrac1p (AN)^{1/p}\bigr), & p < 0, \end{cases}$$

and $W_0$, $W_{-1}$ are the principal and lower branches of the Lambert $W$ function. Then for each fixed integer $k \ge 0$,

$$\lambda T_{N-k,N} - b_N \xrightarrow{d} Y_k, \qquad \mathbb P(Y_k \le y) = \frac{\Gamma(k+1, e^{-y})}{k!}, \quad y \in \mathbb R,$$

where $\Gamma(a, z) = \int_z^\infty u^{a-1} e^{-u}\, du$. Equivalently $Y_k \overset{d}{=} -\ln(E_1 + \dots + E_{k+1})$ with $E_1, E_2, \dots$ independent unit-rate exponential variables; $Y_0$ is standard Gumbel, $\mathbb P(Y_0 \le y) = \exp(-e^{-y})$. Jointly,

$$\bigl(\lambda T_{N-k,N} - b_N, \dots, \lambda T_{N,N} - b_N\bigr) \xrightarrow{d} \bigl(-\ln(E_1 + \dots + E_{k+1}), \dots, -\ln E_1\bigr).$$

The admissible choice $b_N = \ln(AN) - p \ln\ln\bigl(\tfrac1p (AN)^{1/p}\bigr) - p \ln p$ (terms in $p$ read as $0$ when $p = 0$) follows from $W_0(z) = \ln z - \ln\ln z + o(1)$ as $z \to \infty$ and $W_{-1}(z) = \ln(-z) - \ln(-\ln(-z)) + o(1)$ as $z \to 0^-$.

## Expansion

The count of searchers still unfinished at time $t_N(y) = (y + b_N)/\lambda$ is binomial with parameters $N$ and $S(t_N(y))$. The choice of $b_N$ makes $N S(t_N(y)) \to e^{-y}$, so the count converges to a Poisson variable with mean $e^{-y}$, and $\{T_{N-k,N} \le t_N(y)\}$ is the event that at most $k$ searchers remain, whose limit probability is $\sum_{i=0}^{k} e^{-\mu}\mu^i/i! = \Gamma(k+1, \mu)/k!$ with $\mu = e^{-y}$. The Lambert function solves $A(\lambda t)^{-p} e^{-\lambda t} = e^{-y}/N$ to leading order. The joint limit is the Poisson point process with intensity $e^{-y}\,dy$ formed by the rescaled slowest times; its points in decreasing order are $-\ln(E_1 + \dots + E_j)$, $j = 1, 2, \dots$

## Sources

- S. D. Lawley and J. Johnson, *Slowest first passage times, redundancy, and menopause timing*, J. Math. Biol. (2023), <https://doi.org/10.1007/s00285-023-01921-9>; arXiv:2206.09255. Theorem 1 and Corollary 3; exact law, equation (6).
