# Generalized tau function $\tau_{2p}$ modulo $p$

Let $p$ be an odd prime, let $\tau_k$ be
the generalized tau function, and for an integer $r$ let $P(r) = r(3r - 1)/2$ be the generalized
pentagonal number. For every integer $n \ge 0$,

$$\tau_{2p}(n + 1) \equiv \sum (-1)^{r + s} \pmod p,$$

the sum running over the pairs of integers $r, s$ with $|r| \le n$, $|s| \le n$ and
$n = p\,(P(r) + P(s))$.

The paper prints the side condition as $n + 1 = p(P(r) + P(s))$, which is false: at $n = 0$ the
left side is $\tau_{2p}(1) = 1$ while that sum is empty. The identity
$\sum_{n \ge 0} \tau_{2p}(n + 1) q^n \equiv \prod_{m \ge 1} (1 - q^{pm})^2 \pmod p$ from the
paper's proof gives $n = p(P(r) + P(s))$.

## Sources

- S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024), Article A39, Theorem 16.
