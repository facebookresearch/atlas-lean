# Universal inference: the split likelihood-ratio statistic is an e-value

Let $p_\theta$ be probability densities (nonnegative, total mass at most $1$) with respect to a reference measure on the inference-split space, the data split as $z = (D_0, D_1)$ with $D_0$ the inference split and $D_1$ the estimation split, $\hat\theta_1(D_1)$ any estimator fitted on $D_1$, and the joint law $P_{\theta^*} \otimes \nu$ with $\nu$ an arbitrary probability law of $D_1$ (and the reference measure s-finite). Let $\hat\theta_0$ be a null maximum-likelihood estimator over $\Theta_0$ on the inference split, $\theta^* \in \Theta_0$ with $p_{\theta^*}$ measurable, and $T = p_{\hat\theta_1(D_1)}(D_0)/p_{\hat\theta_0(D_0)}(D_0)$ the split likelihood-ratio statistic, assumed measurable. Then $T$ is an e-value under $P_{\theta^*} \otimes \nu$, whatever the estimator $\hat\theta_1$.

## Sources

- Wasserman, Ramdas and Balakrishnan (2020), proof of Theorem 3.
