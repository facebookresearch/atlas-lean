# Sound and complete abstractions are optimal

Let $\alpha, \gamma$ between $L_1$ and $L_2$ and $\alpha', \gamma'$ between $L_1'$ and $L_2'$ be Galois connections between complete lattices, and let $c : L_1 \to L_1'$ and $a : L_2 \to L_2'$ be monotone.

1. Suppose moreover that $\alpha \circ \gamma$ is the identity of $L_2$ (a *Galois insertion*). If $a$ is a [sound and complete abstraction](sound-optimal-and-complete-abstractions.md) of $c$, that is, $a \circ \alpha = \alpha' \circ c$, then $a$ is the optimal abstraction $\alpha' \circ c \circ \gamma$ of $c$.
2. Some sound and complete abstraction of $c$ exists if and only if the optimal abstraction of $c$ is sound and complete.

The converse of part 1 fails: abstract addition in sign analysis is optimal but not complete. By part 2, sound and complete abstractions do not always exist.

**Proof.** Part 1: $a = a \circ \alpha \circ \gamma = \alpha' \circ c \circ \gamma$. Part 2 needs no insertion: for every Galois connection $\alpha \circ \gamma \circ \alpha = \alpha$, so if $a$ is sound and complete, then $\alpha' \circ c \circ \gamma \circ \alpha = a \circ \alpha \circ \gamma \circ \alpha = a \circ \alpha = \alpha' \circ c$, and the optimal abstraction is sound and complete; the converse direction is immediate.

The hypothesis that $\alpha \circ \gamma$ is the identity cannot be dropped from part 1. Take $L_1 = L_1'$ a one-point lattice, $L_2 = L_2'$ the two-element chain $0 < 1$, $\alpha = \alpha'$ the constant map to $0$, $\gamma = \gamma'$ the unique map, and $c$ the identity. The monotone map $a$ with $a(0) = 0$ and $a(1) = 1$ is sound and complete, since $a \circ \alpha = \alpha' \circ c$, but the optimal abstraction maps $1$ to $0$.

## Depends on

- [Sound, optimal and complete abstractions](sound-optimal-and-complete-abstractions.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 12.2 (the remark that $\alpha \circ \gamma$ is in many cases the identity function, and Exercise 12.14 for sign analysis); Section 12.5, Exercise 12.46 (sound and complete implies optimal, but not conversely, compare Exercises 12.36 and 12.43) and Exercise 12.47 (a sound and complete abstraction exists if and only if the optimal abstraction is sound and complete). The exercises are stated for Galois connections; the hypothesis $\alpha \circ \gamma = \mathrm{id}$ in part 1, the proofs and the counterexample above are written out here.
