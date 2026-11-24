# Kernel mean embeddings and maximum mean discrepancy

A probability measure $P$ on $X$ whose feature map $x \mapsto k(\cdot, x)$ is Bochner integrable is represented by its kernel mean embedding $\mu_P = \mathbb{E}_{x \sim P}\, k(\cdot, x)$, an element of the reproducing kernel Hilbert space $H$ of a positive-definite kernel $k$; it represents expectation, $\langle f, \mu_P \rangle = \mathbb{E}_P f$ for every $f \in H$. For two such measures, the maximum mean discrepancy $\mathrm{MMD}(P, Q) = \sup_{\|f\|_H \le 1} (\mathbb{E}_P f - \mathbb{E}_Q f)$ is the integral probability metric of the unit ball of $H$, and equals $\|\mu_P - \mu_Q\|_H$; its square is a combination of kernel expectations, estimated from samples by V- and U-statistics. A kernel is characteristic when $P \mapsto \mu_P$ is injective on these measures, so that the MMD vanishes only for equal laws; universal kernels on compact metric spaces are characteristic. These are the objects of the kernel two-sample test of Gretton, Borgwardt, Rasch, Schölkopf and Smola (JMLR 2012).

The pages follow Section 2 of the paper: the feature map and kernel of a real reproducing kernel Hilbert space, the mean embedding and its reproducing property (Lemma 3), the MMD as a distance between embeddings (Lemma 4) and its kernel expression (Lemma 6), the biased and unbiased empirical estimates (equations (2), (3) and (5)), and characteristic and universal kernels (Theorem 5).

- [Canonical feature map of a reproducing kernel Hilbert space](reproducing-kernel/README.md)
- [Kernel mean embedding](kernel-mean-embedding/README.md)
- [Maximum mean discrepancy](maximum-mean-discrepancy/README.md)
- [Characteristic kernels](characteristic-kernels/README.md)
- [Unbiased estimator of the squared maximum mean discrepancy](empirical-mmd/README.md)
- [Biased empirical MMD](biased-empirical-mmd/README.md)

## Related topics

- [Positive-definite kernels](../../../Analysis/hilbert-spaces/positive-definite-kernels/README.md): Aronszajn's theorem, every positive-definite kernel is the kernel of a reproducing kernel Hilbert space, which is where the embeddings live.
- [Representer theorem](../../../Analysis/hilbert-spaces/representer-theorem/README.md): the same reproducing property, $f(x) = \langle f, k(\cdot, x) \rangle$, applied to empirical risks instead of expectations.
- [Total variation distance](../total-variation-distance/README.md): for probability measures, twice the total variation distance $\sup_B |P(B) - Q(B)|$ is the integral probability metric of the measurable functions with $|f| \le 1$, where the MMD uses the unit ball of an RKHS.
- [Bochner's theorem](../../characteristic-functions/bochner-s-theorem/README.md): positive-definite continuous functions on $\mathbb{R}$ are characteristic functions of finite measures; on $\mathbb{R}^d$ this is the spectral measure $\Lambda$ of a translation-invariant kernel, whose support decides whether the kernel is characteristic.
- [Random Fourier features](../../../ComputerScience/machine-learning/supervised-learning/random-fourier-features/README.md): Monte Carlo features for shift-invariant kernels, sampled from the same spectral measure $\Lambda$ whose support decides whether the kernel is characteristic.
