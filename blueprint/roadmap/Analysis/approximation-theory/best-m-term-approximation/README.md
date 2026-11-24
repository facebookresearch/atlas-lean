# Best M-term approximation

Nonlinear approximation in an orthonormal basis $(b_i)$ approximates $f$ by combinations of at most $M$ basis vectors whose indices may depend on $f$ (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7 (1998), Section 2). Because the basis is orthonormal, the error of any such approximant is [explicit](norm-sub-sum-smul-sq.md): $\|f - \sum_{i \in T} a_i b_i\|^2 = \sum_{i \in T} |\langle b_i, f\rangle - a_i|^2 + \sum_{i \notin T} |\langle b_i, f\rangle|^2$. For a fixed support the best coefficients are the inner products, and the [error of keeping a set of coefficients](norm-sub-sum-inner-smul-sq.md) is the energy of the others. Since [the largest weights have the largest sum](sum-le-sum-of-forall-le.md), the [best $M$-term approximation](norm-sub-sum-inner-smul-le.md) keeps the $M$ largest coefficients, and its error is the sum of the squares of all the other coefficients, DeVore's identity $\sigma_M(f)^2 = \sum_{k > M} \gamma_k(f)^2$ for the decreasing rearrangement $\gamma_k(f)$ of the coefficients.

This is thresholding: in a wavelet basis it approximates piecewise regular signals with far fewer terms than a linear approximation by the first $M$ vectors, which is the basis of wavelet compression and denoising (R. A. DeVore, *Nonlinear approximation*, Section 3.6 for the Haar basis and Section 7.4 for wavelet bases). The statements here are for a finite orthonormal basis.

- [Error of an $M$-term approximation in an orthonormal basis](norm-sub-sum-smul-sq.md)
- [Error of keeping the coefficients on a set](norm-sub-sum-inner-smul-sq.md)
- [The largest weights have the largest sum](sum-le-sum-of-forall-le.md)
- [Best $M$-term approximation in an orthonormal basis](norm-sub-sum-inner-smul-le.md)

## Related topics

- [Matching pursuit](../matching-pursuit/README.md): in a redundant dictionary the best $M$-term approximation is no longer obtained by sorting coefficients, and greedy pursuits replace it; in an orthonormal basis matching pursuit selects the coefficients in decreasing order and recovers the best $M$-term approximations.
- [Best approximation in normed spaces](../best-approximation-in-normed-spaces/README.md): for a fixed support, the best approximation from the span of the selected basis vectors is the orthogonal projection.
