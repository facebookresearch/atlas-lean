# EM log-likelihood as a sum of HMM log-likelihoods

For every [valid parameter](valid.md) $\theta$, the [log-likelihood](log-lik-le-em-step.md) equals $\sum_n \log L_\theta(x^{(n)})$, where $L_\theta(x)$ is the likelihood of $x_0, \dots, x_T$ under the [HMM of $\theta$](to-hmm.md): the total weight of all state paths.
