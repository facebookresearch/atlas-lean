# Closed-form partition probability of a finite symmetric Dirichlet mixture

Let $\alpha \in \mathbb{R}$, $K, n \in \mathbb{N}$, and let $\pi$ be a partition of $\{1, \dots, n\}$ into $K_+ = |\pi|$ blocks. The finite-mixture partition probability is

$$P_K(\pi) = \frac{K!}{(K - K_+)!} \Big(\frac{\alpha}{K}\Big)^{K_+} \prod_{B \in \pi} \prod_{j=1}^{|B| - 1} \Big(j + \frac{\alpha}{K}\Big) \Big/ \alpha^{(n)},$$

where $\alpha^{(n)} = \alpha(\alpha + 1) \cdots (\alpha + n - 1)$ is the rising factorial ($= \Gamma(n + \alpha)/\Gamma(\alpha)$ for $\alpha > 0$), $K!/(K - K_+)! = K(K-1)\cdots(K - K_+ + 1)$ is the falling factorial (so $P_K(\pi) = 0$ when $K < K_+$), $\alpha/K$ is read as $0$ when $K = 0$, and the whole expression is $0$ when $\alpha^{(n)} = 0$.

Griffiths and Ghahramani (2011, Section 2.2) give this expression as the probability that, in a Bayesian mixture with $K$ classes, weights $\theta \sim \mathrm{Dirichlet}(\alpha/K, \dots, \alpha/K)$ and assignments drawn independently from $\theta$, the assignments induce the partition $\pi$: it is their Equation 4 multiplied by the $K!/K_0!$ ($K_0 = K - K_+$) ways of labelling the blocks with distinct classes. The definition is that closed form; its derivation from the Dirichlet–multinomial model is in the source.

## Informally uses

- [Evidence-weighted Dirichlet prior](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/with-density-categorical-seq-kernel.md): the marginal probability $B(\alpha + \text{counts})/B(\alpha)$ of an assignment vector under the Dirichlet prior (Griffiths and Ghahramani 2011, Equation 3), from which the paper derives Equation 4.

## Sources

- Thomas L. Griffiths and Zoubin Ghahramani, *The Indian buffet process: an introduction and review*, J. Mach. Learn. Res. 12 (2011), 1185–1224, Section 2.2, Equations 3–4.
