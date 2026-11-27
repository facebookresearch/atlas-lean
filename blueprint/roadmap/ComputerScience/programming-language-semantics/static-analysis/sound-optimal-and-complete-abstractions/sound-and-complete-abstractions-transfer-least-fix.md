# Sound and complete abstractions transfer least fixed points

Let $\alpha : L_1 \to L_2$ and $\gamma : L_2 \to L_1$ form a Galois connection between complete lattices, and let $c : L_1 \to L_1$ and $a : L_2 \to L_2$ be monotone, so that both have least fixed points by the Knaster–Tarski theorem. If $a$ is a [sound and complete abstraction](sound-optimal-and-complete-abstractions.md) of $c$, that is, $a \circ \alpha = \alpha \circ c$, then

$$\alpha(\mathrm{lfp}(c)) = \mathrm{lfp}(a).$$

So an analysis whose constraint function is a sound and complete abstraction of the semantic constraint function computes exactly the abstraction of the semantics of the program.

**Proof.** Let $y = \mathrm{lfp}(a)$.
- $\alpha(\mathrm{lfp}(c)) \sqsubseteq y$: we have $\alpha(c(\gamma(y))) = a(\alpha(\gamma(y))) \sqsubseteq a(y) = y$, because $\alpha \circ \gamma$ is reductive and $a$ is monotone. By the adjunction, $c(\gamma(y)) \sqsubseteq \gamma(y)$, so $\gamma(y)$ is a pre-fixed point of $c$ and $\mathrm{lfp}(c) \sqsubseteq \gamma(y)$, since [the least fixed point lies below every pre-fixed point](the-least-fixed-point-lies-below-every-pre-fixed.md). By the adjunction again, $\alpha(\mathrm{lfp}(c)) \sqsubseteq y$.
- $y \sqsubseteq \alpha(\mathrm{lfp}(c))$: $a(\alpha(\mathrm{lfp}(c))) = \alpha(c(\mathrm{lfp}(c))) = \alpha(\mathrm{lfp}(c))$, because [the least fixed point is a fixed point](the-least-fixed-point-is-a-fixed-point.md); so $\alpha(\mathrm{lfp}(c))$ is a fixed point of $a$, hence a pre-fixed point, and $y \sqsubseteq \alpha(\mathrm{lfp}(c))$.

The first inclusion uses only soundness; the second uses completeness.

## Depends on

- [Sound, optimal and complete abstractions](sound-optimal-and-complete-abstractions.md)

## Proof depends on

- [The least fixed point is a fixed point](the-least-fixed-point-is-a-fixed-point.md)
- [The least fixed point lies below every pre-fixed point](the-least-fixed-point-lies-below-every-pre-fixed.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 12.3 (the soundness theorem, $\mathrm{lfp}(c) \sqsubseteq \gamma(\mathrm{lfp}(a))$ when $c \circ \gamma \sqsubseteq \gamma \circ a$) and Section 12.5, Exercise 12.48 (the soundness and completeness theorem: if the analysis constraint function is sound and complete with respect to the semantic constraint function, the abstraction of the semantics of the program equals the analysis result). The proof above is written out here.
