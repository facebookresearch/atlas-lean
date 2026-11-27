# Fredman–Saks lower bound for dynamic prefix parity

Let a deterministic step-indexed cell-probe scheme in $S \le 2^w$ cells of $w$ bits implement dynamic prefix parity on arrays of length $n$, with every update probing at most $t_u$ cells and every query at most $t_q$ cells (worst case). Let $\beta = \max(4, 8 t_u (2w + 1))$. Then, for an absolute constant $c$,

$$
\log_\beta n \le c\, t_q + 1 .
$$

In particular $t_q = \Omega\left(\log n / \log(t_u (w+1))\right)$.

## Proof sketch

The hard instance has $L$ epochs; epoch $j$ writes $\beta^{L-j}$ random bits at spread-out positions so that a query at a random position recovers, from its answer, a fresh parity of the bits of every epoch. Updates of later epochs probe few cells in total compared with the number of bits of epoch $j$, so by the overlay lemma a decoder that knows the later cells can reproduce all queries that avoid the cells last probed in epoch $j$. If queries rarely probed those cells, the bits of epoch $j$ could be encoded in fewer bits than their entropy, a contradiction; hence a typical query probes a cell of a constant fraction of the epochs, and summing over epochs gives the bound.

## Depends on

- [Dynamic prefix parity problem](dynamic-prefix-parity.md)
- [Deterministic dynamic cell-probe scheme](deterministic-cell-probe-scheme.md)

## Proof depends on

- [Overlay lemma for the chronogram method](overlay-lemma-for-the-chronogram-method.md)

## Sources

- M. L. Fredman and M. E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", Proceedings of the 21st ACM Symposium on Theory of Computing (STOC), pp. 345-354, 1989.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), pp. 932-963, 2006.
