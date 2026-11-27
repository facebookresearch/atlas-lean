# Approximately stable committee

Let $C$ be a finite set of candidates with positive weights $s : C \to \mathbb{R}_{>0}$, extended additively to sets, and $N$ a nonempty finite set of $n \ge 1$ voters, each with a weak order $\succeq_i$ on subsets of $C$ that is monotone ($S \subseteq S'$ implies $S' \succeq_i S$). For a weight limit $K > 0$ and $c \ge 1$, a committee $W$ with $s(W) \le K$ is $c$-approximately stable if for every nonempty committee $W' \subseteq C$ (equivalently, every $W'$ with $s(W') > 0$), the number of voters with $W' \succ_i W$ is strictly less than

$$
c \cdot \frac{s(W')}{K} \cdot n .
$$

The empty challenger is excluded because, by monotonicity, no voter strictly prefers $\emptyset$ to $W$, so for $W' = \emptyset$ the condition would read $0 < 0$ and no committee would qualify. For $c = 1$ this is stability, which for approval-additive preferences and unit weights is the core of the committee election.

## Depends on

- [Core of an approval-based committee election](core-of-approval-committee-election.md)

## Sources

- Z. Jiang, K. Munagala, K. Wang, "Approximately Stable Committee Selection", STOC 2020, arXiv:1910.14008.
