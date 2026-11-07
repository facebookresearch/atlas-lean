# Park–Pham theorem on selector processes (Talagrand's selector process conjecture)

There is
a real number $L > 0$ with the following property. Let $0 < p < 1$, let $X$ be a finite type,
let $\Lambda$ be a set of functions from $X$ to $[0, \infty)$, and let $X_p$ be a binomial random
subset of $X$ with parameter $p$. Write
$E = \mathbb{E}\bigl[\sup_{f \in \Lambda} \sum_{i \in X_p} f(i)\bigr]$, computed in
$[0, \infty]$. If $0 < E < \infty$, then the family of subsets $s \subseteq X$ with
$\sup_{f \in \Lambda} \sum_{i \in s} f(i) \ge L E$ is $p$-small.

The hypothesis $0 < E < \infty$ is not stated explicitly in the paper's theorem, but it is used
in the last step of the proof, which derives a contradiction from an inequality $E \ge c E$
with a constant $c > 1$.

## Sources

- J. Park and H. T. Pham, `On a conjecture of Talagrand on selector processes and a consequence on positive empirical processes`, Annals of Math, 199 (3) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_supremum_of_selector_processes` of the lean-eval benchmark.
