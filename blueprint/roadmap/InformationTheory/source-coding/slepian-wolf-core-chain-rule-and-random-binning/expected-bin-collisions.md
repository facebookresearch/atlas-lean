# Expected bin collisions

Let $k, M$ be natural numbers with $M > 0$. For a binning $b : \{0, \dots, k-1\} \to \{0, \dots, M-1\}$ let $C(b) = \#\{(i, j) : i < j,\ b(i) = b(j)\}$ be its number of colliding pairs. Averaging over all $M^k$ binnings,

$$\frac{1}{M^k} \sum_{b} C(b) = \frac{\binom{k}{2}}{M},$$

since each pair $i < j$ collides under a uniformly random binning with probability $1/M$.
