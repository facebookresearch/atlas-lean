# Unique long-only optimum under positivity on feasible differences

Let $\Sigma$ be a real symmetric matrix, and let $W$ be the nonempty set of long-only portfolios with a given expected return ($w \ge 0$, $\sum_i w_i = 1$, $\mu^{\mathsf T}w = m$). If $(w - v)^{\mathsf T}\Sigma(w - v) > 0$ for all distinct $w, v \in W$, then $w^{\mathsf T}\Sigma w$ has at most one minimizer on $W$; together with existence of a minimizer, it has exactly one. Positive definiteness of $\Sigma$, or positivity of $d^{\mathsf T}\Sigma d$ for every nonzero $d$ with $\sum_i d_i = 0$ and $\mu^{\mathsf T}d = 0$, is sufficient but not necessary; if $W$ is a single point the condition is vacuous and its point is the minimizer.

Proof. If $w \ne v$ both attain the minimum $q$, then $(w + v)/2 \in W$ by convexity, and by symmetry of $\Sigma$, $\big(\frac{w+v}{2}\big)^{\mathsf T}\Sigma\frac{w+v}{2} = \frac{q + q}{2} - \frac14(w - v)^{\mathsf T}\Sigma(w - v) < q$, a contradiction.

## Depends on

- [Long-only portfolios with a given expected return](target-slice.md): long-only portfolios with a given expected return.

## Background

- [Long-only minimum of a quadratic form is attained](exists-is-min-on-target-slice.md): existence of a minimizer.
- [Positive definite covariance gives a unique long-only optimum](exists-unique-is-min-on-target-slice-of.md): the positive definite case.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
