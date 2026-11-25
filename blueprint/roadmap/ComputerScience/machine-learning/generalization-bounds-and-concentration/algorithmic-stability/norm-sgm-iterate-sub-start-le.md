# SGM moves at most $L \sum_t \alpha_t$ from its start

Let every loss $\ell(\cdot, z)$ be $L$-Lipschitz on a real Hilbert space and let the steps satisfy $\alpha_t \ge 0$. Then along every index sequence the [iterates of the stochastic gradient method](sgm-iterate.md) satisfy

$$
\lVert w_t - w_0 \rVert \le L \sum_{s < t} \alpha_s .
$$

Proof: each step $w_{s+1} = w_s - \alpha_s \nabla_w \ell(w_s, z_{i_s})$ moves the iterate by at most $\alpha_s L$, since [the gradient update of a Lipschitz function is $\alpha L$-bounded](../../../../Analysis/convex-analysis-and-variations/gradient-descent/norm-smul-gradient-le.md); sum over the steps.

Consequently, if the loss is bounded at the start, $\lvert \ell(w_0, z)\rvert \le M$, then every loss along the run satisfies $\lvert \ell(w_t, z)\rvert \le M + L^2 \sum_{s<t} \alpha_s$, which is what [the generalization bound for SGM](abs-integral-empirical-risk-sub-risk-sgm.md) needs.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Lemma 3.3 (each gradient update is $\alpha L$-bounded), summed over the steps.
