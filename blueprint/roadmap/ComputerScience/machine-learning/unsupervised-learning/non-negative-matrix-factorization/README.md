# Non-negative matrix factorization

- [Objective of nonnegative matrix factorization](objective.md)
- [Nonnegativity of the NMF objective](objective-nonneg.md)
- [The NMF objective is invariant under transposition](objective-transpose.md)
- [Existence of a minimizer](exists-minimizer.md)

## Lee–Seung multiplicative updates

- [Lee–Seung multiplicative update of H](update-h.md)
- [Lee–Seung multiplicative update of W](update-w.md)
- [One sweep of the Lee–Seung algorithm](sweep.md)
- [The W update is the H update of the transposed problem](update-w-eq-transpose.md)
- [The Lee–Seung H update preserves nonnegativity](update-h-nonneg.md)
- [The Lee–Seung W update preserves nonnegativity](update-w-nonneg.md)
- [Lee–Seung, `H` step](objective-update-h-le.md)
- [Lee–Seung, `W` step](objective-update-w-le.md)
- [A Lee–Seung sweep preserves nonnegativity](sweep-nonneg.md)
- [One Lee–Seung sweep does not increase the objective](objective-sweep-le.md)
- [The objective is non-increasing along the Lee–Seung iterates](objective-sweep-iterate-antitone.md)

## Stationarity at fixed points

- [Gradient of the NMF objective with respect to H](grad-h.md)
- [Gradient of the NMF objective with respect to W](grad-w.md)
- [Partial derivative of the NMF objective in an entry of H](has-deriv-at-objective-h.md)
- [Partial derivative of the NMF objective in an entry of W](has-deriv-at-objective-w.md)
- [Complementary slackness at a fixed point of the `H` update](mul-grad-h-eq-zero-of-update-h-eq.md)
- [Complementary slackness at a fixed point of the `W` update](mul-grad-w-eq-zero-of-update-w-eq.md)
- [Karush–Kuhn–Tucker point of nonnegative matrix factorization](is-kktpoint.md)
- [Positive fixed points are KKT points](is-kktpoint-of-sweep-eq.md)

## Identifiability under separability

- [Separable factor matrix](is-separable.md)
- [A nonnegative matrix with a nonnegative inverse is monomial](exists-perm-of-mul-eq-one.md)
- [Essential uniqueness of NMF when both factors are separable](eq-of-is-separable.md)

## Nonnegative rank

- [Nonnegative rank of a matrix](nonneg-rank.md)
- [A nonnegative factorization bounds the nonnegative rank](nonneg-rank-le-of-mul-eq.md)
- [Existence of a factorization of nonnegative-rank inner dimension](exists-mul-eq-nonneg-rank.md)
- [Nonnegative rank is at most the number of columns](nonneg-rank-le-card-width.md)
- [The nonnegative rank of a nonnegative matrix is at least its rank](rank-le-nonneg-rank.md)

## Applications

- [Column sums of a matrix product](sum-mul-apply.md)
- [Mutational signatures](sum-mul-apply-of-sum-eq-one.md)
- [Gene-expression deconvolution](mul-apply-mem-icc.md)
