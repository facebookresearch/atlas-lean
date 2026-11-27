# Holenstein's local embedding lemma

A distribution $P_0$ of pairs $(x, y)$ is *$\varepsilon$-embeddable* in a distribution $P_1$ of $((x,y),(s,t))$ if Alice, holding $x$, and Bob, holding $y$, can use shared randomness and no communication to output $s$ and $t$ so that $((x,y),(s,t))$ is within statistical distance $\varepsilon$ of $P_1$. Let $J$ be a joint distribution of $((X, Y), S)$ with conditional laws $P_{S|XY}$, $P_{S|X}$, $P_{S|Y}$, and let $\varepsilon_1, \varepsilon_2$ be the distances of $J$ from $P_{XY}P_{S|X}$ and $P_{XY}P_{S|Y}$. Then $P_{XY}$ is $(2\varepsilon_1 + 2\varepsilon_2)$-embeddable in the law of $((X, Y), (S, S))$: Alice and Bob run correlated sampling on $P_{S|X=x}$ and $P_{S|Y=y}$. For another input distribution $P_0$, measuring $\varepsilon_1, \varepsilon_2$ against $P_0P_{S|X}$ and $P_0P_{S|Y}$, the error is at most $7\varepsilon_1 + 2\varepsilon_2$. If $s$ depends only on $x$ and $t$ only on $y$, the embedding is exact with private randomness; embeddability is monotone in $\varepsilon$, transitive with additive errors, and preserved by maps.

## Proof sketch

For fixed $(x, y)$ the two local samples are each within their kernel distances of $P_{S|XY}$, and correlated sampling makes them disagree with probability at most twice the distance between the two local kernels. Averaging over $(x, y)$ and the triangle inequality give $2\varepsilon_1 + 2\varepsilon_2$; the change of input distribution adds further triangle-inequality terms.

## Depends on

- [Holenstein's correlated sampling from a distribution-independent seed](correlated-sampling-shared-seed.md)

## Proof depends on

- [Holenstein's correlated sampling from a distribution-independent seed](correlated-sampling-shared-seed.md)

## Sources

- T. Holenstein, "Parallel Repetition: Simplifications and the No-Signaling Case", Theory of Computing, 2009.
