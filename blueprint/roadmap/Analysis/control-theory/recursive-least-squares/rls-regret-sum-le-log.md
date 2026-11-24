# Logarithmic regret of the least-squares adaptive predictor

In the setting of [the convergence rate of recursive least squares](rls-error-sq-le-log-div-lambda-min.md)
($y_{k+1} = \varphi_k^\top \theta + w_{k+1}$, adapted regressors, martingale-difference noise with
$\sup_k E[|w_{k+1}|^\beta \mid \mathcal F_k] < \infty$ for some $\beta > 2$), the best predictor of $y_{k+1}$ given
$\mathcal F_k$ is $\varphi_k^\top \theta$ and the adaptive predictor built from the RLS estimate is
$\varphi_k^\top \theta_k$. Their squared difference $R_k = (\varphi_k^\top (\theta_k - \theta))^2$ is the regret. If
$\varphi_t^\top P_t \varphi_t$ is bounded in $t$ almost surely, then almost surely, on the event
$\sum_{k \le t} |\varphi_k|^2 \to \infty$, there is $C$ with

$$\sum_{k \le t} R_k \le C \log\Big(1 + \sum_{k \le t} |\varphi_k|^2\Big)$$

for all large $t$. No excitation condition is assumed: the predictions become good on average even when the
parameter itself is not identified. This is the property on which the analysis of least-squares-based self-tuning
regulators rests, since the certainty-equivalence control makes $\varphi_k^\top \theta_k$ equal to the reference.

Source: Xie, Zhang and Guo, *Convergence of a distributed least squares*, IEEE Trans. Automat. Control, accepted version (2020), DOI 10.1109/TAC.2020.3047989, Theorem 3.2 with one sensor.

**Differences from the source.** As on the companion page, the statement assumes $E|w_{k+1}|^\beta < \infty$ and is
restricted to the event $\sum_k |\varphi_k|^2 = \infty$, where $\log(1 + \sum_{k \le t} |\varphi_k|^2)$ and the source's
$\log r_t$ differ by a factor tending to one. Without the restriction the bound cannot hold literally: with
$P_0 = 100 I$ in dimension one, $\varphi_0 = 0.1$ and $\varphi_k = 0$ for $k \ge 1$, $r_t = 0.01 + 0.01 = 0.02$, so
$\log r_t < 0$, while $R_0 = 0.01 (\theta_0 - \theta)^2 > 0$ whenever $\theta_0 \ne \theta$. (The source's $O(b_t)$ is defined only for positive $b_t$, Section II.A; here $\log r_t \le 0$, so the stated bound is either undefined or, read as $\|A_t\| \le M \log r_t$, false.)

## Informally uses

- [Logarithmic bound on the accumulated RLS gains](sum-rls-gain-le-log-det.md): the source's proof of Theorem 3.1,
  from which Theorem 3.2 follows, bounds the noise contribution by inequality (33).
- [The RLS matrix is the inverse of the information matrix](rls-snd-eq-inv.md): the matrix inversion lemma in the same
  proof.
