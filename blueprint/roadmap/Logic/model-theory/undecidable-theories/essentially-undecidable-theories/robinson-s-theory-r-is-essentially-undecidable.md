# Robinson's theory R is essentially undecidable

The Tarski–Mostowski–Robinson theory R, whose axioms are infinitely many true numerical facts about addition, multiplication and order, is essentially undecidable: every consistent extension of R in its language is undecidable.

**The theory R.** The language has $0$, $\mathsf{S}$, $+$ and $\times$; numerals are $\underline{n} = \mathsf{S}^n 0$, and $u \leq t$ abbreviates $\exists w\,(w + u = t)$. The axioms of R are, for all natural numbers $m, n$:

1. $\underline{m} + \underline{n} = \underline{m + n}$;
2. $\underline{m} \times \underline{n} = \underline{m \cdot n}$;
3. $\underline{m} \neq \underline{n}$ for $m \neq n$;
4. $\forall x\,(x \leq \underline{n} \to x = \underline{0} \vee \cdots \vee x = \underline{n})$;
5. $\forall x\,(x \leq \underline{n} \vee \underline{n} \leq x)$.

**Theorem (Tarski, Mostowski and Robinson).** A first-order theory $U$ is *essentially undecidable* if every consistent extension of $U$ in the same language is undecidable. The theory R is essentially undecidable.

Cobham strengthened this: R is essentially hereditarily undecidable, so also every consistent recursively enumerable theory in the same language that is contained in a consistent extension of R is undecidable (Theorem 3.9 of arXiv:2212.03565v2, there for the variant of R with $<$ as a primitive symbol).

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

R is strong enough to represent every recursive function, since representability only needs the numerical axioms and the bounded-quantifier axioms 4 and 5; the diagonal argument used for Q then applies to every consistent extension of R. A good expansion links pages for representability of recursive functions in R and for the diagonal argument, which have none yet.

## Sources

- A. Tarski, A. Mostowski and R. M. Robinson, *Undecidable Theories*, Studies in Logic and the Foundations of Mathematics, North-Holland, 1953 (original source, cited beside the copy read).
- J. Murwanashyaka, F. Pakhomov and A. Visser, "There are no minimal essentially undecidable theories", *Journal of Logic and Computation* 34(6):1159–1171, 2024, doi:10.1093/logcom/exad005; read as arXiv:2207.08174v2, <https://arxiv.org/abs/2207.08174v2>: Section 2 ("Salient examples of essentially undecidable theories are R and Q").
- A. Visser, "Essential hereditary undecidability", *Archive for Mathematical Logic* 63(5–6):529–562, 2024, doi:10.1007/s00153-024-00911-y; read as arXiv:2212.03565v2, <https://arxiv.org/abs/2212.03565v2>: Section 2.2 (the axioms of R and the remark after them on the original version, with $\leq$ defined by $u \leq t$ iff $\exists w\, w + u = t$) and Theorem 3.9 (Cobham).
