# Kernel mean embeddings and maximum mean discrepancy

A probability measure $P$ on $X$ whose feature map $x \mapsto k(\cdot, x)$ is Bochner integrable is represented by its kernel mean embedding $\mu_P = \mathbb{E}_{x \sim P}\, k(\cdot, x)$, an element of the reproducing kernel Hilbert space $H$ of a positive-definite kernel $k$; it represents expectation, $\langle f, \mu_P \rangle = \mathbb{E}_P f$ for every $f \in H$. For two such measures, the maximum mean discrepancy $\mathrm{MMD}(P, Q) = \sup_{\|f\|_H \le 1} (\mathbb{E}_P f - \mathbb{E}_Q f)$ is the integral probability metric of the unit ball of $H$, and equals $\|\mu_P - \mu_Q\|_H$; its square is a combination of kernel expectations, estimated from samples by V- and U-statistics. A kernel is characteristic when $P \mapsto \mu_P$ is injective on these measures, so that the MMD vanishes only for equal laws; universal kernels on compact metric spaces are characteristic. These are the objects of the kernel two-sample test of Gretton, Borgwardt, Rasch, Schölkopf and Smola (JMLR 2012).

The pages follow Section 2 of the paper: the feature map and kernel of a real reproducing kernel Hilbert space, the mean embedding and its reproducing property (Lemma 3), the MMD as a distance between embeddings (Lemma 4) and its kernel expression (Lemma 6), the biased and unbiased empirical estimates (equations (2), (3) and (5)), and characteristic and universal kernels (Theorem 5).

## Feature map and kernel

- [Canonical feature map of a reproducing kernel Hilbert space](feature-map.md)
- [Scalar kernel of a real reproducing kernel Hilbert space](kernel-value.md)
- [Reproducing property of the feature map](inner-feature-map.md)
- [Kernel functions are feature maps](feature-map-apply.md)
- [Symmetry of the kernel](kernel-value-comm.md)
- [The kernel of an RKHS is a positive-definite kernel](is-pos-def-kernel-kernel-value.md)
- [The kernel Gram matrix of the representer theorem](kernel-gram-apply.md)
- [Norm of a feature map](norm-feature-map.md)
- [Operator-valued and scalar kernels](kernel-eq-smul.md)
- [Continuity of the feature map](continuous-feature-map-of-continuous-ker.md)

## The mean embedding

- [Kernel mean embedding](mean-embedding.md)
- [Existence of the kernel mean embedding](integrable-feature-map-of-integrable-sqr.md)
- [Mean embeddings exist for continuous kernels on compact spaces](integrable-feature-map-of-continuous.md)
- [Elements of an RKHS are integrable against measures with integrable feature map](integrable-apply.md)
- [Reproducing property of the kernel mean embedding](inner-mean-embedding.md)
- [The mean embedding as a function](mean-embedding-apply.md)
- [Inner product of two mean embeddings](inner-mean-embedding-mean-embedding.md)
- [Integrability of the kernel on a product](integrable-kernel-value-prod.md)
- [Inner product of mean embeddings as an expectation over independent copies](inner-mean-embedding-eq-integral-prod.md)

## The maximum mean discrepancy

For every kernel the MMD is a pseudometric on probability measures with integrable feature map: it vanishes on the diagonal, is symmetric and satisfies the triangle inequality, because it is a distance between embeddings. It is a metric, $\mathrm{MMD}(P, Q) = 0 \Rightarrow P = Q$, exactly when the kernel is characteristic (below).

- [Maximum mean discrepancy over the unit ball of an RKHS](mmd.md)
- [The unit ball attains the norm of a vector](is-greatest-inner-closed-ball.md)
- [The MMD is the distance between mean embeddings](mmd-eq-norm-sub.md)
- [The MMD vanishes on the diagonal](mmd-self.md)
- [Symmetry of the MMD](mmd-comm.md)
- [Triangle inequality for the MMD](mmd-le-add.md)
- [Population MMD in terms of the kernel](mmd-sq-eq.md)

## Empirical estimates

- [Empirical mean embedding](empirical-embedding.md)
- [Biased empirical MMD](mmd-biased.md)
- [Reproducing property of the empirical mean embedding](inner-empirical-embedding.md)
- [The biased empirical MMD is the distance between empirical mean embeddings](mmd-biased-eq.md)
- [Inner product of empirical mean embeddings](inner-empirical-embedding-empirical-embe.md)
- [The biased empirical MMD as a V-statistic](mmd-biased-sq-eq.md)
- [Unbiased empirical estimate of the squared MMD](mmd-unbiased-sq.md)
- [Two coordinates of an i.i.d. sample are independent copies](measure-preserving-pair-pi.md)
- [The unbiased MMD statistic is unbiased](integral-mmd-unbiased-sq.md)

## Characteristic and universal kernels

- [Characteristic kernel](is-characteristic.md)
- [The MMD of a characteristic kernel separates probability measures](mmd-eq-zero-iff-of-is-characteristic.md)
- [The MMD of a universal kernel characterizes distributions](mmd-eq-zero-iff-of-universal.md)
- [Universal kernels are characteristic](is-characteristic-of-universal.md)
- [Characterization of characteristic translation-invariant kernels](is-characteristic-iff-support-eq-univ.md)

## Related topics

- [Positive-definite kernels](../../../Analysis/hilbert-spaces/positive-definite-kernels/README.md): Aronszajn's theorem, every positive-definite kernel is the kernel of a reproducing kernel Hilbert space, which is where the embeddings live.
- [Representer theorem](../../../Analysis/hilbert-spaces/representer-theorem/README.md): the same reproducing property, $f(x) = \langle f, k(\cdot, x) \rangle$, applied to empirical risks instead of expectations.
- [Total variation distance](../total-variation-distance/README.md): for probability measures, twice the total variation distance $\sup_B |P(B) - Q(B)|$ is the integral probability metric of the measurable functions with $|f| \le 1$, where the MMD uses the unit ball of an RKHS.
- [Bochner's theorem](../../characteristic-functions/bochner-s-theorem/README.md): positive-definite continuous functions on $\mathbb{R}$ are characteristic functions of finite measures; on $\mathbb{R}^d$ this is the spectral measure $\Lambda$ of a translation-invariant kernel, whose support decides whether the kernel is characteristic.
- [Random Fourier features](../../../ComputerScience/machine-learning/supervised-learning/random-fourier-features/README.md): Monte Carlo features for shift-invariant kernels, sampled from the same spectral measure $\Lambda$ whose support decides whether the kernel is characteristic.
