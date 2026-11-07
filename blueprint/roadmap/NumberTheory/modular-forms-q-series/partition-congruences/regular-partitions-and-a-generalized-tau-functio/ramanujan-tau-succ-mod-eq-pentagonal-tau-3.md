# Ramanujan's $\tau$ modulo $19$ via $\tau_5$

Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,

$$\tau(n + 1) \equiv \sum_{19P(r) \le n} (-1)^r \tau_5(n - 19P(r) + 1) \pmod{19},$$

the sum running over all integers $r$ with $19P(r) \le n$.

The source record prints $\tau_5(s)$ in place of $\tau_5(s + 1)$, where $n = 19P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^5 (1 - q^{19m}) = \sum_{r, s} (-1)^r \tau_5(s + 1) q^{19P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

## Sources

- S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 12 (`integers-2024-A39-thm-12`).
