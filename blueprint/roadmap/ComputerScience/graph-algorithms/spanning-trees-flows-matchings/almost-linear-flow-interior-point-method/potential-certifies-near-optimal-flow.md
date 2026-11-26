# A very negative IPM potential certifies a near-optimal flow

Let $\mathbf{f}$ lie in the domain of the potential $\Phi$ of *Potential function of the l1 interior point method for minimum-cost flow*. Then

$$
\Phi(\mathbf{f}) \ge 20m \log\bigl(\mathbf{c}^{\top}\mathbf{f} - F^*\bigr).
$$

Consequently, if $\Phi(\mathbf{f}) \le -200 m \log(mU)$ then $\mathbf{c}^{\top}\mathbf{f} - F^* \le (mU)^{-10}$.

## Proof sketch

Both barrier terms $(\mathbf{u}^+_e - \mathbf{f}_e)^{-\alpha}$ and $(\mathbf{f}_e - \mathbf{u}^-_e)^{-\alpha}$ are positive because $\mathbf{f}$ is strictly inside the box, so dropping them lower-bounds $\Phi$. Rearranging $20m\log(\mathbf{c}^{\top}\mathbf{f} - F^*) \le -200m\log(mU)$ gives $\log(\mathbf{c}^{\top}\mathbf{f} - F^*) \le -10\log(mU)$.

## Depends on

- [Potential function of the l1 interior point method for minimum-cost flow](l1-ipm-potential-function.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
