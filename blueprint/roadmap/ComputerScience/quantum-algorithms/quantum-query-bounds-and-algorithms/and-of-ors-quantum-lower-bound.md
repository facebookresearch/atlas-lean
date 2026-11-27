# The AND of √N ORs needs Ω(√N) quantum queries

Split $N = s w$ bits into $s$ blocks of $w$ bits and let $f$ be the AND over blocks of the OR within the block (Tribes is its De Morgan dual). Every $T$-query algorithm computing $f$ with error at most $\varepsilon$, where $0 \le \varepsilon < 1/2$, satisfies $\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\sqrt{s w} \le 2T$, so $Q(f) = \Omega(\sqrt N)$ for $s = w = \sqrt N$, whereas block sensitivity $\Theta(\sqrt N)$ yields only $\Omega(N^{1/4})$ through the polynomial or hybrid method.

## Proof sketch

Relate inputs with exactly one true bit in every block to inputs obtained by clearing the true bit of one block (which makes the AND false); each yes-input has $s$ partners, each no-input $w$ partners (choosing which position of the empty block to set), and each index distinguishes at most one partner, giving $\sqrt{sw}$ by Ambainis's bound.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)
- [Decision-tree depth and degree of a Boolean function](../../../TheoryOfComputation/communication-complexity/query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

- [Ambainis adversary bound](../quantum-query-lower-bounds/ambainis-adversary-bound.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002, Theorem 4 (case $s = w = \sqrt N$).
