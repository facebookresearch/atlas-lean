# The NPG normalizer is bounded by the next policy's advantage

Along natural policy gradient, for every state $s$,

$$\log Z_t(s) \le \frac{\eta}{1-\gamma} \sum_a \pi_{t+1}(a \mid s)\, A^{\pi_t}(s,a),$$

the gap being the relative entropy of $\pi_{t+1}(\cdot \mid s)$ from $\pi_t(\cdot \mid s)$.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, proof of Lemma 5.2
