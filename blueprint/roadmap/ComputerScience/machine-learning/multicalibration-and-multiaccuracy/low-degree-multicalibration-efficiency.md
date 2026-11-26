# Low-degree multicalibration captures the guarantees of multicalibration at lower cost

Low-degree multicalibration of a fixed small degree already implies key consequences of full multicalibration: for degree $2$ (multiaccuracy plus correlation with $p(x)$) it implies the fairness-type guarantees on identifiable groups and accuracy improvements that multiaccuracy alone does not give, and it suffices for omniprediction with respect to suitable loss classes. Its sample and time complexity are comparable to multiaccuracy; in the multiclass setting with $\ell$ labels, the sample complexity of degree-$k$ multicalibration is polynomial in $\ell$ for fixed $k$, an exponential improvement in $\ell$ over full multicalibration, whose complexity grows exponentially with the number of classes.

## Proof sketch

Degree-$k$ multicalibration is multiaccuracy with respect to the product class $\{c(x)\, w(p(x))\}$, and polynomials of degree $k$ in $\ell$ variables span a space of dimension $\binom{\ell + k}{k}$, so the boosting algorithm converges in a number of rounds independent of the discretization of the $\ell$-dimensional simplex. The consequences are proved by showing that each uses only low-degree tests of the predictor's level sets.

## Depends on

- [Low-degree multicalibration](low-degree-multicalibration.md)
- [Multiaccurate predictors](multiaccurate-predictor.md)
- [Multicalibrated predictors](multicalibrated-predictor.md)
- [Omnipredictors](../outcome-indistinguishability-and-omniprediction/omnipredictor.md)

## Proof depends on

- [Multicalibration by iterated level-set corrections terminates quickly](multicalibration-iterative-algorithm.md)

## Sources

- P. Gopalan, M. P. Kim, M. Singhal, S. Zhao, "Low-Degree Multicalibration", COLT (2022), arXiv:2203.01255.
