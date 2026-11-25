# Convergence rate of recursive least squares under martingale-difference noise

Let $(\mathcal F_k)$ be a filtration, $\theta \in \mathbb R^d$ and $y_{k+1} = \varphi_k^\top \theta + w_{k+1}$, where
the regressor $\varphi_k$ and the noise $w_k$ are $\mathcal F_k$-measurable (so $\varphi_k$ may be computed by feedback
from past outputs), $E[w_{k+1} \mid \mathcal F_k] = 0$, and for some $\beta > 2$,
$\sup_k E[|w_{k+1}|^\beta \mid \mathcal F_k] < \infty$ almost surely. Let $\theta_t$ be the RLS estimate from
$\theta_0$ and a positive definite $P_0$. Then almost surely, on the event $\sum_{k \le t} |\varphi_k|^2 \to \infty$,
there is $C$ with

$$\lambda_{\min}(t) \, |\theta_{t+1} - \theta|^2 \le C \log\Big(1 + \sum_{k \le t} |\varphi_k|^2\Big)$$

for all large $t$, where $\lambda_{\min}(t)$ is the smallest eigenvalue of $P_0^{-1} + \sum_{k \le t} \varphi_k \varphi_k^\top$.
In particular $\theta_t \to \theta$ almost surely on the event where
$\log(1 + \sum_{k \le t} |\varphi_k|^2) / \lambda_{\min}(t) \to 0$ and $\sum_k |\varphi_k|^2 = \infty$, the Lai–Wei
excitation condition, which requires no independence, stationarity or persistent excitation.

Source: Xie, Zhang and Guo, *Convergence of a distributed least squares*, IEEE Trans. Automat. Control, accepted version (2020), DOI 10.1109/TAC.2020.3047989, Theorem 3.3 with $n = 1$ sensor and graph diameter $D_G = 1$ (their Remark 3.3); the paper's
introduction and Remark 3.3 attribute the single-sensor theory to Lai and Wei (Ann. Statist. 10 (1982)) and to Chen and
Guo (*Identification and Stochastic Adaptive Control*, Birkhäuser 1991), which were not consulted directly.

**Differences from the source.** The smallest eigenvalue enters through its lower bounds $\ell$
($\ell \, |x|^2 \le x^\top (P_0^{-1} + \sum_{k \le t} \varphi_k \varphi_k^\top) x$ for all $x$), which is
equivalent. The statement also assumes $E|w_{k+1}|^\beta < \infty$, so that the conditional moments are defined. It is restricted to the event $\sum_k |\varphi_k|^2 = \infty$, on which
$\log(1 + \sum_{k \le t} |\varphi_k|^2)$ and the source's $\log r_t$, $r_t = \lambda_{\max}(P_0^{-1}) + \sum_{k \le t} |\varphi_k|^2$,
differ by a factor tending to one. Without such a restriction the bound $O(\log r_t / \lambda_{\min}(t))$ cannot hold
literally in degenerate cases: with $P_0 = I$ and $\varphi_k = 0$ for all $k$, $r_t = 1$ and $\log r_t = 0$, while
$\theta_t = \theta_0$ for all $t$, so the error is $|\theta_0 - \theta|^2 \ne 0$ whenever $\theta_0 \ne \theta$. (The source's $O(b_t)$ is defined only for positive $b_t$, Section II.A; here $\log r_t \le 0$, so the stated bound is either undefined or, read as $\|A_t\| \le M \log r_t$, false.)

The hypotheses are jointly satisfiable in a non-degenerate way: $d = 1$, $\varphi_k = 1$, and $w_k$ independent standard
Gaussian variables with $\mathcal F_k = \sigma(w_1, \dots, w_k)$; then $\lambda_{\min}(t) = P_0^{-1} + t + 1$ and the
statement gives $|\theta_{t+1} - \theta|^2 = O(\log t / t)$.

## Informally uses

- [The RLS matrix is the inverse of the information matrix](rls-snd-eq-inv.md): the proof of Theorem 3.1 of the source,
  on which Theorem 3.3 rests, applies the matrix inversion lemma to the recursion.
- [Logarithmic bound on the accumulated RLS gains](sum-rls-gain-le-log-det.md): inequality (33) of the source, which
  bounds the noise contribution in the proof of Theorem 3.1 by $\log \det P_{t+1}^{-1}$.

## Background

- [Martingales and optional stopping](../../../Probability/martingales/README.md): the source's proof uses a martingale
  estimation theorem for $\sum_k a_k w_{k+1}$ with adapted weights.
- [Convergence of noise-free RLS under growing excitation](tendsto-rls-fst-of-noise-free.md): the deterministic case,
  where any growth of the smallest eigenvalue suffices.
