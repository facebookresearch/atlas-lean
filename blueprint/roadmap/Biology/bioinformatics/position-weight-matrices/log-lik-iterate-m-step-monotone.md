# The motif likelihood is nondecreasing along the EM iterates

Under the hypotheses of [the M-step maximizes the EM objective](em-q-le-em-q-m-step.md), for every positive matrix $\theta_0$ the sequence $k \mapsto \sum_m \log \sum_z p_{\theta_k}(x^{(m)}, z)$ is nondecreasing, where $\theta_{k+1}$ is the [M-step](m-step.md) of $\theta_k$ and $p$ the [motif model](motif-model.md).
