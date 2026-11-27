# Debiased machine learning: finite-sample Gaussian approximation

Assume the setting of [Riesz representer and the doubly robust moment](riesz-representer-and-doubly-robust-moment.md): $\theta_0 = \mathbb E\{m(W,\gamma_0)\}$ with mean-square continuity constants $(\bar Q, q)$ and minimal representer $\alpha_0^{\min}$.

Let $(Y_i, W_i)$, $i = 1, \dots, n$, be independent copies of $(Y, W)$.

**Algorithm (cross-fitted DML).** Partition $\{1,\dots,n\}$ into $L$ folds $I_1,\dots,I_L$ of equal size $n/L$. For each $\ell$, fit $\hat\gamma_\ell, \hat\alpha_\ell$ on $I_\ell^c$. Set

$$\hat\theta = \frac1n \sum_{\ell=1}^L \sum_{i \in I_\ell}\Big[m(W_i,\hat\gamma_\ell) + \hat\alpha_\ell(W_i)\{Y_i - \hat\gamma_\ell(W_i)\}\Big],$$

$\hat\sigma^2$ the average squared deviation of the bracketed terms from $\hat\theta$, and report $\hat\theta \pm c_a\hat\sigma n^{-1/2}$ with $c_a$ the $1-a/2$ standard normal quantile.

Let $\psi_0(w) = m(w,\gamma_0) + \alpha_0^{\min}(w)\{y - \gamma_0(w)\} - \theta_0$, which has mean zero by the doubly robust moment, $\sigma^2 = \mathbb E\psi_0^2$, assumed positive and finite, $\kappa^3 = \mathbb E|\psi_0|^3$, $\zeta^4 = \mathbb E\psi_0^4$, $c_{BE} = 0.4748$ (an upper bound for the [Berry–Esseen constant](../../../../../Probability/central-limit-theorems/optimal-berry-esseen-constant/upper-bounds/shevtsova2011-upper-bound-holds.md)), and for each fold $R(\hat\gamma_\ell) = \mathbb E[\{\hat\gamma_\ell(W) - \gamma_0(W)\}^2 \mid \{(Y_i, W_i) : i \in I_\ell^c\}]$ for an independent copy $W$, $R(\hat\alpha_\ell)$ likewise. Write $R_\gamma = \max_\ell R(\hat\gamma_\ell)$ and $R_\alpha = \max_\ell R(\hat\alpha_\ell)$, so that the bounds below hold uniformly over the folds.

**Theorem (finite-sample Gaussian approximation).** Suppose mean-square continuity holds, $\mathbb E[\{Y-\gamma_0(W)\}^2\mid W] \le \bar\sigma^2$ and $\|\alpha_0^{\min}\|_\infty \le \bar\alpha$. Then with probability at least $1-\epsilon$,

$$\sup_{z \in \mathbb R}\Big|\mathrm{pr}\Big\{\frac{n^{1/2}}{\sigma}(\hat\theta-\theta_0) \le z\Big\} - \Phi(z)\Big| \le c_{BE}\Big(\frac{\kappa}{\sigma}\Big)^3 n^{-1/2} + \frac{\Delta}{(2\pi)^{1/2}} + \epsilon,$$

$$\Delta = \frac{3L}{\epsilon\sigma}\Big[(\bar Q^{1/2} + \bar\alpha)R_\gamma^{q/2} + \bar\sigma R_\alpha^{1/2} + (n R_\gamma R_\alpha)^{1/2}\Big].$$

**Corollary (validity of the interval).** As $n \to \infty$ with $L$ fixed, if in addition $\{(\kappa/\sigma)^3 + \zeta^2\}\, n^{-1/2} \to 0$ (the factor $n^{-1/2}$ multiplies the whole sum; $(\kappa/\sigma)^3 \ge 1$ by Lyapunov's inequality, so it cannot itself tend to zero), $\|\hat\alpha_\ell\|_\infty \le \bar\alpha'$ for every $\ell$, $(\bar Q^{1/2} + \bar\alpha/\sigma + \bar\alpha')R_\gamma^{q/2} = o_p(1)$, $\bar\sigma R_\alpha^{1/2} = o_p(1)$ and $(nR_\gamma R_\alpha)^{1/2}/\sigma = o_p(1)$, then $\hat\theta \to \theta_0$, $\sigma^{-1}n^{1/2}(\hat\theta - \theta_0) \Rightarrow N(0,1)$, and $\mathrm{pr}\{\theta_0 \in \hat\theta \pm c_a\hat\sigma n^{-1/2}\} \to 1-a$.

The product term $(nR_\gamma R_\alpha)^{1/2}$ is the double robustness: one nuisance may be learned slowly if the other is learned fast enough.

## Depends on

- [Riesz representer and the doubly robust moment of a linear functional](riesz-representer-and-doubly-robust-moment.md)

## Proof depends on

- [Shevtsova's 2011 Berry–Esseen bound](../../../../../Probability/central-limit-theorems/optimal-berry-esseen-constant/upper-bounds/shevtsova2011-upper-bound-holds.md)

## Expansion

Write $\hat\theta - \theta_0 = n^{-1}\sum_i \psi_0(W_i) + \mathrm{remainder}$. The leading term is an average of $n$ independent, mean-zero copies of $\psi_0(W)$ with variance $\sigma^2 > 0$, handled by the Berry–Esseen bound with constant $c_{BE}$. The remainder splits per fold into two linear terms, controlled by mean-square continuity and by $R(\hat\gamma_\ell)$, $R(\hat\alpha_\ell)$ (cross-fitting makes them conditionally mean zero given $I_\ell^c$), and one bilinear term $\mathbb E[(\hat\alpha_\ell - \alpha_0^{\min})(\gamma_0 - \hat\gamma_\ell)]$, bounded by Cauchy–Schwarz by $\{R(\hat\gamma_\ell)R(\hat\alpha_\ell)\}^{1/2}$; Markov's inequality converts these into the probability-$1-\epsilon$ statement.

## Sources

- Victor Chernozhukov, Whitney K. Newey and Rahul Singh, "A simple and general debiased machine learning theorem with finite-sample guarantees", Biometrika 110 (2023), 257–264, <https://doi.org/10.1093/biomet/asac033>; author manuscript <https://par.nsf.gov/servlets/purl/10471116>. Numbering of the published journal edition: Algorithm 1, Definition 1, Theorem 1 and Corollary 1 (arXiv:2105.15197 numbers them differently).
