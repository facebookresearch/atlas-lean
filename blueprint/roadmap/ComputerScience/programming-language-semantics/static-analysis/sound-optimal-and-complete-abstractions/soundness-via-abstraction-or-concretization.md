# Soundness via abstraction or concretization

Let $\alpha, \gamma$ between $L_1$ and $L_2$ and $\alpha', \gamma'$ between $L_1'$ and $L_2'$ be Galois connections between complete lattices, and let $c : L_1 \to L_1'$ and $a : L_2 \to L_2'$ be monotone. Then

$$\alpha' \circ c \sqsubseteq a \circ \alpha \quad\text{if and only if}\quad c \circ \gamma \sqsubseteq \gamma' \circ a,$$

so a [sound abstraction](sound-optimal-and-complete-abstractions.md) can equivalently be defined through the concretization functions. The analogous equivalence fails for completeness.

For programs, take endomaps $c : L_1 \to L_1$ and $a : L_2 \to L_2$ with one Galois connection $\alpha, \gamma$ between $L_1$ and $L_2$. Then the analysis is sound for the program, $\alpha(\mathrm{lfp}(c)) \sqsubseteq \mathrm{lfp}(a)$, if and only if $\mathrm{lfp}(c) \sqsubseteq \gamma(\mathrm{lfp}(a))$.

**Proof.** If $\alpha' \circ c \sqsubseteq a \circ \alpha$, then for $y \in L_2$, $\alpha'(c(\gamma(y))) \sqsubseteq a(\alpha(\gamma(y))) \sqsubseteq a(y)$, since $\alpha \circ \gamma$ is reductive and $a$ monotone; by the adjunction, $c(\gamma(y)) \sqsubseteq \gamma'(a(y))$. Conversely, if $c \circ \gamma \sqsubseteq \gamma' \circ a$, then for $x \in L_1$, $c(x) \sqsubseteq c(\gamma(\alpha(x))) \sqsubseteq \gamma'(a(\alpha(x)))$, so $\alpha'(c(x)) \sqsubseteq a(\alpha(x))$. The statement about programs is the adjunction applied to $\mathrm{lfp}(c)$ and $\mathrm{lfp}(a)$.

## Depends on

- [Sound, optimal and complete abstractions](sound-optimal-and-complete-abstractions.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 12.3, Exercise 12.30 (the two definitions of soundness of an analysis are equivalent under a Galois connection) and Exercise 12.34 (soundness of abstractions via abstraction or concretization functions); Section 12.5, Exercises 12.40 and 12.41 (the equivalence does not hold for completeness). The proof above is written out here.
