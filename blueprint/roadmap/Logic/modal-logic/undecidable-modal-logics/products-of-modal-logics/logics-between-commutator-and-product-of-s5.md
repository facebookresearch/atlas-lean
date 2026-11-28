# Logics between the commutator and the product of n copies of S5 are undecidable for n ≥ 3

For every $n \geq 3$, every $n$-modal logic that lies between the commutator of $n$ copies of S5 and their product is undecidable; algebraically, this is Maddux's undecidability for diagonal-free cylindric algebras.

**Theorem (Maddux).** Let $n \geq 3$. Every $n$-modal logic $L$ with

$$
[\mathbf{S5}, \dots, \mathbf{S5}] \subseteq L \subseteq \mathbf{S5}^n
$$

(see [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)) is undecidable (Theorem 43 of the survey read).

The logic $\mathbf{S5}^n$ does not even have the finite model property for $n \geq 3$.

## Depends on

- [products and commutators of modal logics](products-and-commutators-of-modal-logics.md)
- [Extra axioms of S5](../../normal-modal-logics/s5.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The uniform word problem for Thue systems is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-thue-wp.md)

## Expansion

Maddux worked in the algebraic setting of diagonal-free cylindric algebras of dimension $n$, the algebraic counterparts of these logics, and reduced the word problem for semigroups. Another proof, via the connection between $\mathbf{S5}^n$ and the $n$-variable fragment of first-order logic, reduces the $\omega \times \omega$ tiling problem. The source names the word problem for semigroups; the linked page states the uniform word problem for Thue systems, that is, for finitely presented monoids. A good expansion also links the correspondence between these logics and diagonal-free cylindric algebras.

## Sources

- R. Maddux, "The equational theory of $\mathrm{CA}_3$ is undecidable", *Journal of Symbolic Logic* 45(2):311–316, 1980, doi:10.2307/2273191 (original source, cited beside the copy read).
- A. Kurucz, "Combining modal logics", in P. Blackburn, J. van Benthem and F. Wolter (eds.), *Handbook of Modal Logic*, Studies in Logic and Practical Reasoning 3, Elsevier, 2007, pp. 869–924, doi:10.1016/S1570-2464(07)80018-8; read in the author's open-access copy at <https://kuag19.github.io/homepage/combi.pdf>: Theorem 43 and the paragraph before it.
