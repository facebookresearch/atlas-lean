# Logarithmic regret of the least-squares adaptive predictor

Let $y_{k+1} = \varphi_k^\top \theta + w_{k+1}$, with regressors $\varphi_k$ adapted to $(\mathcal F_k)$,
and adapted martingale-difference noise $w_{k+1}$. For some $\beta > 2$, suppose $E|w_{k+1}|^\beta < \infty$
for each $k$ and $\sup_k E[|w_{k+1}|^\beta \mid \mathcal F_k] < \infty$ almost surely; this uniform bound may
depend on the sample path. Start [recursive least squares](rls.md) from any estimate $\theta_0$ and a
positive definite matrix $P_0$. The regret $R_k = (\varphi_k^\top(\theta_k - \theta))^2$ is the squared difference
between the adaptive predictor $\varphi_k^\top \theta_k$ and the oracle signal $\varphi_k^\top \theta$.
The latter is the conditional mean when $y_{k+1}$ is integrable.

If $\varphi_t^\top P_t \varphi_t$ is bounded in $t$ almost surely, then almost surely, on the event
$\sum_{k \le t} |\varphi_k|^2 \to \infty$, there is a path-dependent $C$ with

$$\sum_{k \le t} R_k \le C \log\Big(1 + \sum_{k \le t} |\varphi_k|^2\Big)$$

for all large $t$. No growth in every regressor direction is required. The bound implies vanishing
average regret if $\log(1 + \sum_{k \le t} |\varphi_k|^2) = o(t)$.

## Sources

- Xie, Zhang and Guo, *Convergence of a distributed least squares*, IEEE Trans. Automat. Control, accepted version (2020), DOI 10.1109/TAC.2020.3047989, Theorem 3.2 with one sensor.

**Differences from the source.** The statement explicitly assumes $E|w_{k+1}|^\beta < \infty$ and is
restricted to the event $\sum_k |\varphi_k|^2 = \infty$, where $\log(1 + \sum_{k \le t} |\varphi_k|^2)$ and the source's
$\log r_t$ differ by a factor tending to one. Without that restriction, the source's logarithm may not
be positive: in dimension one take $P_0 = 100 I$, $\varphi_0 = 0.1$ and $\varphi_k = 0$ for $k \ge 1$.
Then $r_t = 0.02$, so $\log r_t < 0$, while $R_0 = 0.01(\theta_0 - \theta)^2 > 0$ whenever
$\theta_0 \ne \theta$. The source defines its $O(b_t)$ notation for positive $b_t$ (Section II.A).
