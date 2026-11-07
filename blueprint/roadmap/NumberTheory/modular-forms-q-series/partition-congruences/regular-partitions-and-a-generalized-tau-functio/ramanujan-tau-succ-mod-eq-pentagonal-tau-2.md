# Ramanujan's $\tau$ modulo $17$ via $\tau_7$

Let $\tau = \tau_{24}$ be Ramanujan's tau
function, where $\tau_k$ is the generalized tau function, and let $P(r) = r(3r - 1)/2$ for
integers $r$. For every integer $n \ge 1$,

$$\tau(n + 1) \equiv \sum_{17P(r) \le n} (-1)^r \tau_7(n - 17P(r) + 1) \pmod{17},$$

the sum running over all integers $r$ with $17P(r) \le n$.

The source record prints $\tau_7(s)$ in place of $\tau_7(s + 1)$, where $n = 17P(r) + s$;
that version is false at $n = 1$. The shifted index comes from the identity
$\prod_{m \ge 1} (1 - q^m)^7 (1 - q^{17m}) = \sum_{r, s} (-1)^r \tau_7(s + 1) q^{17P(r) + s}$,
which follows from Definition 1.1 and is used in the proof.

## Sources

- S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 11 (`integers-2024-A39-thm-11`).
