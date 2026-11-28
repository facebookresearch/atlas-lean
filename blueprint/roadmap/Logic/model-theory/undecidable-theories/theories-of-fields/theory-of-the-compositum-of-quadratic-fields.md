# The theory of the compositum of all quadratic fields is undecidable

The field obtained by adjoining to the rationals all square roots of integers, the compositum of all quadratic extensions of $\mathbb Q$, has an undecidable first-order theory in the language of rings: Robinson's arithmetic $Q$ is interpretable in it.

**Theorem (Martínez-Ranero, Utreras and Videla).** Fix an algebraic closure $\mathbb Q^{\mathrm{alg}}$ of $\mathbb Q$, and let $\mathbb Q^{(2)} \subseteq \mathbb Q^{\mathrm{alg}}$ be the compositum of all field extensions $F/\mathbb Q$ of degree at most $2$; equivalently $\mathbb Q^{(2)} = \mathbb Q(i, \sqrt{p} : p \text{ prime})$. [Robinson's arithmetic $Q$](../../../first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md) is first-order interpretable in $\mathbb Q^{(2)}$, and hence the complete first-order theory $\mathrm{Th}(\mathbb Q^{(2)})$ of $\mathbb Q^{(2)}$ in the language of rings $\{0, 1, +, \cdot\}$ is undecidable: no algorithm decides, given a sentence in this language, whether it holds in $\mathbb Q^{(2)}$.

This places $\mathbb Q^{(2)}$ among the infinite algebraic extensions of $\mathbb Q$ with undecidable theory, alongside every number field (J. Robinson) and the fields $\mathbb Q(\sqrt p : p \in S)$ for an infinite set $S$ of primes (Videla); by contrast $\mathbb Q^{\mathrm{alg}}$ and the real algebraic numbers have decidable theories (Tarski).

## Depends on

- [Robinson's arithmetic Q](../../../first-order-logic/peano-arithmetic-and-robinson-s-q/qtheory.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Robinson arithmetic Q is essentially undecidable](../essentially-undecidable-theories/robinson-arithmetic-q-is-essentially-undecidable.md)
- [Theories interpreting an essentially undecidable theory are undecidable](../essentially-undecidable-theories/theories-interpreting-an-essentially.md)

## Expansion

Write $K = \mathbb Q(\sqrt p : p \text{ prime})$, so $\mathbb Q^{(2)} = K(i)$. Since $\mathbb Q^{(2)}$ is a pro-$2$ Galois extension of $\mathbb Q$, its ring of integers $\mathcal O$ is first-order definable in it (Videla's theorem for pro-$p$ extensions of number fields), so it suffices to interpret $Q$ in $\mathrm{Th}(\mathcal O)$. By a lemma of J. Robinson improved by Henson, the theory of a ring of algebraic integers interprets $Q$ as soon as some formula $\varphi(x; \bar y)$ defines, as the parameters $\bar y$ vary, finite sets of unboundedly large cardinality. The paper exhibits such a family, using that the group of roots of unity of $\mathbb Q^{(2)}$ is finite and Robinson's finiteness of $\{x \in \mathcal O_K : 0 \ll x \ll t\}$ (all conjugates strictly between $0$ and $t$). Since $Q$ is essentially undecidable, any theory interpreting it is undecidable.

## Sources

- C. Martínez-Ranero, J. Utreras and C. R. Videla, "Undecidability of $\mathbb Q^{(2)}$", *Proceedings of the American Mathematical Society* 148(3):961–964, 2020, <https://doi.org/10.1090/proc/14849>; read as arXiv:1809.04670v1, <https://arxiv.org/abs/1809.04670v1>: Main Theorem of Section 1 and its proof in Section 2 (Theorem 2, Lemmas 3 to 7).
