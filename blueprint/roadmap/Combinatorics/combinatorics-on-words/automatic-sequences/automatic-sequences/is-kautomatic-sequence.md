# Automatic sequences via finite automata

Let $k$ be a natural number and $B$ a finite
alphabet. A sequence $w : \mathbb{N} \to B$ is $k$-automatic when $k \ge 2$ and there is a
deterministic finite automaton with output, consisting of a nonempty finite set of states $Q$, an
initial state $s \in Q$, a transition map $\delta : Q \times \{0, 1, \dots, k-1\} \to Q$ and an
output map $\tau : Q \to B$, such that for every $n \in \mathbb{N}$ and every finite word
$d_0 d_1 \cdots d_{m-1}$ of digits in $\{0, 1, \dots, k-1\}$ with $\sum_{i < m} d_i k^i = n$, the
automaton started in $s$ and reading $d_0, d_1, \dots, d_{m-1}$ in this order (least significant
digit first) stops in a state $t$ with $\tau(t) = w(n)$.

## Sources

- Sunic Definition 3, lines 556-560 of `cubefree.tex`. The universal clause over all representing words enforces tolerance of trailing high-order zeros.
