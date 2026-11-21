# The PhyloCSF score

For a coding model $(t_C, \pi_C)$, a non-coding model $(t_N, \pi_N)$ and an alignment $A$ of $m$ columns, the score is

$$\mathrm{sc}(A) = \sum_{k=1}^{m} \log \frac{\mathcal{L}(t_C, \pi_C, A_k)}{\mathcal{L}(t_N, \pi_N, A_k)},$$

where $\mathcal{L}$ is the [site likelihood](site-lik.md), with the conventions $x/0 = 0$, $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$ (natural logarithms).
