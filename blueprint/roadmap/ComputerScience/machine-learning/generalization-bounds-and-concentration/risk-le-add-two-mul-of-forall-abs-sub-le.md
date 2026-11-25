# Empirical risk minimization under a uniform deviation bound

Let $R$ and $\hat R$ be real functions on a class of predictors, let $\hat f$ minimize $\hat R$ over the class, and suppose $|\hat R(f) - R(f)| \le s$ for every predictor $f$ of the class. Then for every $f$ in the class,

$$
R(\hat f) \le R(f) + 2 s.
$$

Proof: $R(\hat f) \le \hat R(\hat f) + s \le \hat R(f) + s \le R(f) + 2 s$.

With the expected and empirical risks, this reduces the estimation error of empirical risk minimization to a uniform deviation bound, the starting point of every bound in this topic.

## Background

- [Uniform deviation of the empirical risk over a finite class](measure-real-exists-abs-empirical-risk-s.md): background, a probabilistic bound on $s$ for a finite class.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 4.4, equation (4.10): $R(\hat f) - R(f) \le (R(\hat f) - \hat R(\hat f)) + (\hat R(\hat f) - \hat R(f)) + (\hat R(f) - R(f))$, with the middle term nonpositive.
