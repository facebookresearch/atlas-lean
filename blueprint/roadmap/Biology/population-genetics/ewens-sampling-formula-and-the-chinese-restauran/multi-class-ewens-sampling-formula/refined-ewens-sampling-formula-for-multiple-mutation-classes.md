# Refined Ewens sampling formula for multiple mutation classes

**Model.** A Wright–Fisher population of $2N$ genes evolves under the infinitely-many-alleles model, with mutations of $k$ distinguishable classes: each gene independently mutates to a brand-new allele of class $l$ with probability $\mu_l$ per generation, $l = 1,\dots,k$. Each allele thus carries the class of the mutation that created it. For a sample of $n$ genes from the stationary population, let $A^{(l)}_{N,j}(n)$ be the number of alleles of class $l$ represented exactly $j$ times, so $\sum_{l=1}^k\sum_{j=1}^n j\,A^{(l)}_{N,j}(n) = n$.

**Theorem.** Let $\mu_l = \theta_l/(4N)$ with fixed $\theta_1,\dots,\theta_k > 0$, and $\theta = \theta_1 + \dots + \theta_k$. As $N \to \infty$, $\big(A^{(l)}_{N,j}(n)\big)$ converges in distribution to $\big(A^{(l)}_j(n)\big)$ with

$$\mathbb P\Big(A^{(l)}_j(n) = a^{(l)}_j\ \forall l, j\Big) = \mathbf 1\Big(\sum_{l=1}^k\sum_{j=1}^n j\,a^{(l)}_j = n\Big)\,\frac{n!}{(\theta)_n}\prod_{l=1}^k\prod_{j=1}^n\left(\frac{\theta_l}{j}\right)^{a^{(l)}_j}\frac{1}{a^{(l)}_j!},$$

where $(\theta)_n = \theta(\theta+1)\cdots(\theta+n-1)$. Summing over classes recovers the Ewens sampling formula with parameter $\theta$. The family of these laws over $n$ is consistent under random deletion of a gene (a multiple partition structure), and it is a mixture of multinomial sampling from a $k$-colored Poisson–Dirichlet law $\mathrm{PD}(\theta_1,\dots,\theta_k)$.

## Expansion

Trace the sample back through the Kingman coalescent: with $p$ lineages, the next event is a coalescence with probability $(p-1)/(p-1+\theta)$ or a mutation of class $l$ with probability $\theta_l/(p-1+\theta)$. A mutation of class $l$ closes off an allelic block colored $l$. This is the Hoppe urn with $k$ colors of "black balls" of weights $\theta_l$, so the uncolored block structure is Ewens$(\theta)$ and colors are assigned independently to blocks with probabilities $\theta_l/\theta$, which gives the product formula. The weak-mutation expansion of one-generation transition probabilities makes the discrete Wright–Fisher chain converge to this coalescent description.

## Sources

- Eugene Strahov, "A refinement of the Ewens sampling formula", Adv. in Appl. Math. 175 (2026), 103043, <https://doi.org/10.1016/j.aam.2026.103043>. Numbering follows the arXiv version, arXiv:2403.05077 (2024): Theorem 1.1, Propositions 2.3, 4.1 and Theorem 3.4, <https://doi.org/10.48550/arXiv.2403.05077>.
