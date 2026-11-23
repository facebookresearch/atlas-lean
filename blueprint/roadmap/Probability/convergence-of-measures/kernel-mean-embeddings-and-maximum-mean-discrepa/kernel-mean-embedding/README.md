# Kernel mean embedding

Let $X$ be a measurable space and $H$ a real reproducing kernel Hilbert space of functions on $X$ with feature map $\varphi$ and kernel $k$. The mean embedding of a measure $P$ on $X$ is the Bochner integral $\mu_P = \int \varphi(x) \, dP(x) \in H$, taken to be $0$ when $\varphi$ is not Bochner integrable for $P$. When $\varphi$ is integrable, every $f \in H$ is $P$-integrable and $\langle f, \mu_P \rangle = \int f \, dP$, so $\mu_P$ represents integration against $P$ on $H$; as a function, $\mu_P(y) = \int k(y, x) \, dP(x)$.

## Idea

The embedding replaces a distribution by a single vector of a Hilbert space, and expectations by inner products: for probability measures $P$ and $Q$ whose feature maps are Bochner integrable and independent $x \sim P$ and $y \sim Q$, $\langle \mu_P, \mu_Q \rangle = \mathbb{E}\, k(x, y)$. With the linear kernel on $\mathbb{R}^d$ the embedding records only the mean of $P$; polynomial kernels record moments up to their degree; for a characteristic kernel such as the Gaussian kernel it determines a probability measure completely. The embedding exists, for instance, when $\varphi$ is almost everywhere strongly measurable for $P$ (as it is when $\varphi$ is measurable and $H$ is separable) and $\int \sqrt{k(x, x)} \, dP(x) < \infty$; the integral condition holds for every finite measure when $k$ is bounded. Distances between embeddings give the maximum mean discrepancy.

## Statements

- [Kernel mean embedding](mean-embedding.md)
- [The mean embedding as a function](mean-embedding-apply.md): the embedding evaluated as a function
- [Reproducing property of the kernel mean embedding](inner-mean-embedding.md): reproducing property of the embedding
- [Inner product of two mean embeddings](inner-mean-embedding-mean-embedding.md): inner product of two embeddings
- [Inner product of mean embeddings as an expectation over independent copies](inner-mean-embedding-eq-integral-prod.md): inner product of two embeddings as an expectation over independent copies
- [Existence of the kernel mean embedding](integrable-feature-map-of-integrable-sqr.md): existence of the embedding
- [Mean embeddings exist for continuous kernels on compact spaces](integrable-feature-map-of-continuous.md): existence, compact continuous case
- [Elements of an RKHS are integrable against measures with integrable feature map](integrable-apply.md): lemma: elements of the space are integrable
- [Integrability of the kernel on a product](integrable-kernel-value-prod.md): lemma: integrability of the kernel on a product, used for the inner-product formula

## Background

- [Reproducing kernel and canonical feature map](../reproducing-kernel/README.md)

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*, Journal of Machine Learning Research (2012).
