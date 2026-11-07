# Ramanujan's $\tau$ modulo $13$ via $\tau_{11}$

Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,

$$\tau(n + 1) \equiv \sum_{13P(r) \le n} (-1)^r \tau_{11}(n - 13P(r) + 1) \pmod{13},$$

the sum running over all integers $r$ with $13P(r) \le n$.

The source record prints $\tau_{11}(s)$ in place of $\tau_{11}(s + 1)$, where $n = 13P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^{11} (1 - q^{13m}) = \sum_{r, s} (-1)^r \tau_{11}(s + 1) q^{13P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

## Sources

- S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 10 (`integers-2024-A39-thm-10`).
