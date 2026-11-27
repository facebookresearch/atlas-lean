# Ambainis: Ω(√N) quantum queries to invert a permutation

Let a $T$-query value-oracle algorithm, given oracle access to a permutation $\pi$ of an $N$-element set and a fixed target $t$, output $\pi^{-1}(t)$ with error at most $\varepsilon \le 1/2$ on every permutation. Then

$$\big(1 - 2\sqrt{\varepsilon(1 - \varepsilon)}\big)\sqrt{\lfloor N/2 \rfloor} \le 2T,$$

and for $N \ge 2$ also $\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\sqrt{N} \le 2\sqrt{3}\,T$; at $\varepsilon = 1/3$ this gives $N \le 3888\, T^2$. Grover search inverts a permutation with $O(\sqrt N)$ queries, so the bound is tight.

## Proof sketch

Partition permutations according to whether $\pi^{-1}(t)$ lies in the first or second half, relate permutations differing by a transposition moving the preimage of $t$ across, and apply the relational adversary bound. With $\lceil N/2 \rceil$ positions in the first half, $m = \lfloor N/2 \rfloor$ and $m' = \lceil N/2 \rceil$ (or vice versa). At a position where the two related permutations differ, one of them has its preimage of $t$ there and all its partners differ there, while the other has exactly one partner differing there; so $L = \lceil N/2 \rceil$ and $\sqrt{mm'/L} = \sqrt{\lfloor N/2 \rfloor}$. For $N \ge 2$, $\lfloor N/2 \rfloor \ge N/3$; at $\varepsilon = 1/3$, $1 - 2\sqrt{2}/3 \ge 1/18$.

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)

## Proof depends on

- [Ambainis: relational adversary bound for non-Boolean input alphabets](ambainis-relational-adversary-for-value-queries.md)
- [Quantum search with an unknown number of marked items (BBHT)](../quantum-query-bounds-and-algorithms/quantum-search-with-unknown-number-of-solutions.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002, Theorem 7 (Ambainis splits by the parity of the preimage position).
