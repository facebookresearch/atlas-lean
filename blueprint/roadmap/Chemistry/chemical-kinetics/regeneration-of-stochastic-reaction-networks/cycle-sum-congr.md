# Cycle sums depend only on the steps before a finite later visit

Let $S$ be a set, $q, g : S \to \mathbb{R}$, $x_0, x \in S$, $j < k$ natural numbers, and
$\omega, \omega'$ step sequences. If the [$k$-th visit](visit.md) to $x_0$ of the jump chain
started at $x$ is finite, $V_k(x_0, x, \omega) = n$, and $\omega'_i = \omega_i$ for every $i < n$,
then the [$j$-th cycle sums](cycle-sum.md) agree:

$$C_j(\omega) = C_j(\omega') .$$

So the $j$-th cycle sum is determined before the stopping time $V_k$, in the sense the
[strong Markov property at an almost surely finite stopping time](map-prod-shift-at.md) asks of the
map it makes independent of the later steps.
