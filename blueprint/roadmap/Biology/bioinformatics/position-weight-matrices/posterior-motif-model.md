# The E-step in closed form

If $q(b) > 0$ for every $b$, then for every positive matrix $\theta$, sequence $x$ and latent $z$, the posterior of the [motif model](motif-model.md) is

$$P(z \mid x, \theta) = \frac{\pi(z)\, r(z)}{\sum_{z'} \pi(z')\, r(z')},$$

where $r$ is the [window ratio](window-ratio.md), with $x/0 = 0$ (Lawrence and Reilly 1990; Bailey and Elkan 1995).

## Sources

- C. E. Lawrence and A. A. Reilly, *An expectation maximization (EM) algorithm for the identification and characterization of common sites in unaligned biopolymer sequences*, Proteins 7 (1990), 41–51.
- T. L. Bailey and C. Elkan, *Fitting a mixture model by expectation maximization to discover motifs in biopolymers*, Proc. ISMB 2 (1994), 28–36; *Unsupervised learning of multiple motifs in biopolymers using expectation maximization*, Machine Learning 21 (1995), 51–80.
