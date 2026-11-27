# Sound, optimal and complete abstractions

Let $L_1$ and $L_2$ be [complete lattices](../../../../Order/lattices-boolean-algebras/complete-lattice.md), $L_1$ for a collecting semantics and $L_2$ for an analysis. Monotone functions $\alpha : L_1 \to L_2$, the *abstraction function*, and $\gamma : L_2 \to L_1$, the *concretization function*, form a *Galois connection* if $x \sqsubseteq \gamma(\alpha(x))$ for all $x \in L_1$ and $\alpha(\gamma(y)) \sqsubseteq y$ for all $y \in L_2$; equivalently, $\alpha(x) \sqsubseteq y \iff x \sqsubseteq \gamma(y)$ for all $x$ and $y$.

Let $\alpha, \gamma$ between $L_1$ and $L_2$ and $\alpha', \gamma'$ between $L_1'$ and $L_2'$ be Galois connections, and let $c : L_1 \to L_1'$ be a monotone semantic function and $a : L_2 \to L_2'$ a monotone function of the analysis. Then $a$ is
- a *sound* abstraction of $c$ if $\alpha' \circ c \sqsubseteq a \circ \alpha$ pointwise;
- the *optimal* (or *best*) abstraction of $c$ if $a = \alpha' \circ c \circ \gamma$;
- a *complete* abstraction of $c$ if $a \circ \alpha \sqsubseteq \alpha' \circ c$ pointwise.

For a program $P$ with semantics $\mathrm{lfp}(c)$ and analysis result $\mathrm{lfp}(a)$, where $c : L_1 \to L_1$ and $a : L_2 \to L_2$, the analysis is *sound* for $P$ if $\alpha(\mathrm{lfp}(c)) \sqsubseteq \mathrm{lfp}(a)$ and *complete* for $P$ if $\mathrm{lfp}(a) \sqsubseteq \alpha(\mathrm{lfp}(c))$.

For example, in sign analysis abstract multiplication is the optimal abstraction of multiplication of sets of integers and is complete, while abstract addition is optimal but not complete: $\{1\} + \{-1\} = \{0\}$, yet the signs $+$ and $-$ add to the top element.

## Depends on

- [Complete lattice](../../../../Order/lattices-boolean-algebras/complete-lattice.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>:
    - Section 12.2: abstraction and concretization functions, the two properties of a Galois connection, and Exercise 12.17 (equivalence with the adjunction condition);
    - Section 12.3: soundness of an analysis for a program and the general definition of a sound abstraction;
    - Section 12.4: the optimal abstraction $\alpha' \circ c \circ \gamma$, with footnote 6 on the term "best", and optimality of the sign operators (Exercise 12.36);
    - Section 12.5: completeness of an analysis and of an abstraction, completeness of abstract multiplication, and Exercise 12.43 (abstract addition is not complete).
