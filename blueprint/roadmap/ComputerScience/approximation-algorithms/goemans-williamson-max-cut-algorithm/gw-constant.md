# The Goemans–Williamson constant

$$\alpha = \inf_{0 < \theta \le \pi} \frac{2}{\pi} \cdot \frac{\theta}{1 - \cos \theta}.$$

Goemans and Williamson write $\alpha$ as a minimum, attained at $\theta \approx 2.331122$, the
nonzero root of $\cos\theta + \theta \sin\theta = 1$; here it is defined as the infimum, which
needs no attainment. It satisfies $0.87856 < \alpha$ ([Lemma 3.5](lt-gw-constant.md)) and
$\alpha \le 1$ ([at $\theta = \pi$](gw-constant-le-one.md)).

## Background

- [MAX-CUT has no PTAS unless P = NP](../../../TheoryOfComputation/pcp-and-inapproximability/inapproximability-of-max-cut/max-cut-no-ptas.md):
  the unconditional hardness side of the same problem.

## Related topics

- [Majority Is Stablest](../../../Combinatorics/boolean-functions/structure-theorems-for-boolean-functions/majority-is-stablest.md):
  a later result that uses $\alpha$ rather than a prerequisite for it: through
  Khot–Kindler–Mossel–O'Donnell it shows that, assuming the Unique Games Conjecture, no
  polynomial-time algorithm approximates MAX CUT better than $\alpha$.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), §2, p. 1121.
