# Locally testable code

Let $C \subseteq \mathbb{F}_2^n$ be a binary code, let $q$ be a
natural number and let $\kappa \ge 0$ be a real number. A $\kappa$-local tester for $C$ with
$q$ queries consists of a probability distribution on the subsets
$S \subseteq \{0, 1, \dots, n - 1\}$ with at most $q$ elements, together with, for each such
$S$, a set $V_S \subseteq \mathbb{F}_2^S$ of allowed local views, such that:
* if $f \in C$, then $f|_S \in V_S$ for every such $S$;
* for every $f \in \mathbb{F}_2^n$, the probability that $f|_S \notin V_S$ for a random $S$ is
  at least $\kappa$ times the normalised distance from $f$ to $C$.

The code $C$ is $\kappa$-locally testable with $q$ queries exactly when such a tester exists.

## Sources

- Definition 2.3 in `Locally Testable Codes with constant rate, distance, and locality` by I. Dinur, S. Evra, R. Livne, A. Lubotzky and S. Mozes. This probability distribution formulation is also mentioned immediately after Definition 1.1 in the original paper `Good Locally Testable Codes`.
