# Goemans–Williamson Theorem 3.3 with the numerical constant

For nonnegative weights and unit vectors $v_i$,

$$0.87856 \cdot \frac12 \sum_{i<j} w_{ij}(1 - v_i \cdot v_j) \le \sum_{i<j} w_{ij} \frac{\arccos(v_i \cdot v_j)}{\pi}.$$

With [Theorem 3.1](integral-cut-weight-hyperplane.md) and the
[relaxation bound](cut-weight-le-relaxation-value.md), this is the $0.87856$ guarantee of the
random-hyperplane algorithm, in expectation.

## Informally uses

- [Term-by-term comparison](gw-constant-mul-vector-objective-le.md) and
  [Lemma 3.5](lt-gw-constant.md), together with
  [nonnegativity of the objective](vector-objective-nonneg.md).

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), Theorem 3.3 and Lemma 3.5.
