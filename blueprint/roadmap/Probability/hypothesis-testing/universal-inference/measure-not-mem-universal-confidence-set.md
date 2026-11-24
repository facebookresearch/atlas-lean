# Finite-sample validity of the universal confidence set

Let $\Theta$, $\mathcal{Y}$ and $\mathcal{W}$ be measurable spaces, $\nu$ an s-finite measure on $\mathcal{Y}$ (a
countable sum of finite measures), and $q_\theta : \mathcal{Y} \to [0, \infty]$, $\theta \in \Theta$, functions
jointly measurable in $(\theta, y)$ with $\int q_\theta \, d\nu \le 1$ for every $\theta$. Let $\rho$ be a probability
measure on $\mathcal{W}$, $\hat\theta_1 : \mathcal{W} \to \Theta$ a measurable estimator and $\theta^* \in \Theta$. For
$0 < \alpha < \infty$ let $C(w, y) = \{\theta : q_{\hat\theta_1(w)}(y) \le \alpha^{-1} q_\theta(y)\}$. Then

$$(\rho \otimes q_{\theta^*}\nu)\bigl(\{(w, y) : \theta^* \notin C(w, y)\}\bigr) \le \alpha.$$

The measure $q_{\theta^*}\nu$ has mass at most $1$. When $\int q_{\theta^*} \, d\nu = 1$, the measure
$\rho \otimes q_{\theta^*}\nu$ is the law of an independent pair $(D_1, D_0)$ with $D_1 \sim \rho$ and $D_0$ of density
$q_{\theta^*}$, and the bound reads $P(\theta^* \notin C(D_1, D_0)) \le \alpha$.

No regularity of the model is needed: no smoothness, no identifiability, no asymptotics. This is
Theorem 1 in the generality of Remark 2 of Wasserman, Ramdas and Balakrishnan, where $D_0$ may be
any sample with a likelihood; the i.i.d. case of their Theorem 1 is
[the next statement](measure-not-mem-universal-confidence-set-2.md). Ratios are written without division: $T(\theta) \le 1/\alpha$ is
$\mathcal L_0(\hat\theta_1) \le \alpha^{-1} \mathcal L_0(\theta)$ in $[0, \infty]$. This fixes the
convention $0/0 = 0$, which matters only on samples of probability zero under the true parameter.

## Informally uses

- [Markov's inequality for a likelihood ratio](with-density-inv-mul-lt-le.md): applied conditionally on $D_1$, for the fixed alternative $\psi = \hat\theta_1(D_1)$, and then integrated over $D_1$.

## Related topics

- [Coverage of the universal confidence set with real densities](measure-not-mem-universal-confidence-set-3.md): the form with real-valued densities, where only the true density and the split likelihood ratio are assumed measurable.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, arXiv:1912.11436v4 (21 October 2022); published in Proc. Natl. Acad. Sci. USA 117 (2020) 16880–16890. Theorem, remark and equation numbers refer to the arXiv version, which is the one read. Theorem 1 and Remark 2.
