# Ambainis: Ω(√N) quantum queries to invert a permutation

Let a $T$-query value-oracle algorithm, given oracle access to a permutation $\pi$ of an $N$-element set and a fixed target $t$, output $\pi^{-1}(t)$ with error at most $\varepsilon \le 1/2$ on every permutation. Then

$$\big(1 - 2\sqrt{\varepsilon(1 - \varepsilon)}\big)\sqrt{\lfloor N/2 \rfloor} \le 2T,$$

and for $N \ge 2$ also $\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\sqrt{N} \le 2\sqrt{3}\,T$; at $\varepsilon = 1/3$ this gives $N \le 3888\, T^2$. Grover search inverts a permutation with $O(\sqrt N)$ queries, so the bound is tight.

## Proof sketch

Partition permutations according to whether $\pi^{-1}(t)$ lies in the first or second half, relate permutations differing by a transposition moving the preimage of $t$ across, and apply the relational adversary bound with $m, m' \approx N/2$ and $L \approx N/2$ (at the preimage position of $t$, $x$ has all $N/2$ partners differing there and each partner $y$ has one), giving $\sqrt{mm'/L} \approx \sqrt{N/2}$.

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)

## Proof depends on

- [Ambainis: relational adversary bound for non-Boolean input alphabets](ambainis-relational-adversary-for-value-queries.md)

## Sources

- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002.
