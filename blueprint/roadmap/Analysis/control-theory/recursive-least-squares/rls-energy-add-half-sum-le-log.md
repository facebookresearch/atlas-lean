# Joint stochastic energy and prediction-error bound for recursive least squares

On a probability space with filtration $(\mathcal F_k)$, let the regressor $\varphi_k$ and the
noise $w_k$ be $\mathcal F_k$-measurable, and let $y_{k+1} = \varphi_k^\top \theta + w_{k+1}$
for fixed $\theta \in \mathbb R^d$. Assume $\mathbb E[w_{k+1} \mid \mathcal F_k] = 0$ and, for
some $\beta > 2$, assume $\mathbb E|w_{k+1}|^\beta < \infty$ for each $k$ and
$\sup_k \mathbb E[|w_{k+1}|^\beta \mid \mathcal F_k] < \infty$ almost surely.

Start recursive least squares at $(\theta_0,P_0)$ with $P_0$ positive definite, and write
$(\theta_k,P_k)$ for the state after $k$ updates. Set $e_k = \theta_k - \theta$,
$q_k = \varphi_k^\top P_k \varphi_k$, and $V_k = e_k^\top P_k^{-1} e_k$, where
$P_k^{-1} = P_0^{-1} + \sum_{j\lt k} \varphi_j \varphi_j^\top$ is the information matrix.
Almost surely there are finite nonnegative constants $C_0,C_1$ (depending on the path) such that
for all sufficiently large $t$,

$$
V_{t+1} + \tfrac12 \sum_{k=0}^t \frac{(\varphi_k^\top e_k)^2}{1+q_k}
\le C_0 + C_1 \log\!\left(1+\sum_{k=0}^t \|\varphi_k\|_2^2\right).
$$

This is the single-sensor case of Theorem 3.1 of Xie, Zhang and Guo, *Convergence of a
Distributed Least Squares*,
[doi:10.1109/TAC.2020.3047989](https://doi.org/10.1109/TAC.2020.3047989), which bounds the
weighted prediction-error sum and the information-weighted error each by $O(\log r_t)$, where
$r_t = \lambda_{\max}(P_0^{-1}) + \sum_{k=0}^t \|\varphi_k\|_2^2$, combined as in their
Lemma 4.4, whose extra term vanishes for one sensor. Unlike the source, this statement also
assumes $\mathbb E|w_{k+1}|^\beta < \infty$, combines the two parts with coefficient $\tfrac12$
on the sum, and writes $O(\log r_t)$ as $C_0 + C_1 \log(1 + \sum_{k=0}^t \|\varphi_k\|_2^2)$.
It requires neither bounded leverage nor divergence of the regressor energy.
