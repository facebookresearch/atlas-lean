# The optimal abstraction is the most precise sound one

Let $\alpha, \gamma$ between $L_1$ and $L_2$ and $\alpha', \gamma'$ between $L_1'$ and $L_2'$ be Galois connections between complete lattices, and let $c : L_1 \to L_1'$ be monotone. The [optimal abstraction](sound-optimal-and-complete-abstractions.md) $a^\sharp = \alpha' \circ c \circ \gamma$ of $c$ is a sound abstraction of $c$, and every sound abstraction $a$ of $c$ satisfies $a^\sharp \sqsubseteq a$ pointwise.

So, relative to the chosen analysis lattices, the optimal abstraction is the most precise sound abstract counterpart of $c$, although it need not be computable.

**Proof.** Soundness: $\alpha'(c(x)) \sqsubseteq \alpha'(c(\gamma(\alpha(x)))) = a^\sharp(\alpha(x))$, because $x \sqsubseteq \gamma(\alpha(x))$ and $\alpha' \circ c$ is monotone. Minimality: if $a$ is sound, then $a^\sharp(y) = \alpha'(c(\gamma(y))) \sqsubseteq a(\alpha(\gamma(y))) \sqsubseteq a(y)$, because $\alpha \circ \gamma$ is reductive and $a$ is monotone.

Optimality does not compose: the optimal abstractions of two functions need not compose to the optimal abstraction of their composite.

## Depends on

- [Sound, optimal and complete abstractions](sound-optimal-and-complete-abstractions.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 12.4 (the optimal abstraction as the best possible, most precise yet sound, abstraction, obtained by concretizing, applying the semantic function and abstracting; the observation that it gives no practical algorithm) and Section 12.5, Exercise 12.49(b) (optimal abstractions are not closed under composition). The proof above is written out here.
