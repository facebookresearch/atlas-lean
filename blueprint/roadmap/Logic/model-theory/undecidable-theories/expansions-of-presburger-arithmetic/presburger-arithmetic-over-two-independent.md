# Presburger arithmetic over Q(α, β) is undecidable

If $1, \alpha, \beta$ are linearly independent over the rationals, then the truth of sentences about integers built from linear inequalities with coefficients in $\mathbb Q(\alpha, \beta)$ is undecidable, already for four alternating quantifier blocks of $20000$ variables.

**Theorem (Hieronymi, Nguyen and Pak).** Let $\alpha, \beta$ be real numbers such that $1, \alpha, \beta$ are linearly independent over $\mathbb Q$. There is no algorithm that decides, given an $\exists^k\forall^k\exists^k\forall^k$ [$\mathbb Q(\alpha, \beta)$-PA sentence](presburger-arithmetic-with-scalar-multiplication.md) with $k = 20000$, that is, a sentence with four alternating blocks of $k$ integer variables, the first existential, over a Boolean combination of linear inequalities with coefficients and constant terms in $\mathbb Q(\alpha, \beta)$, whether it is true in $\mathbb Z$.

Here $\alpha$ and $\beta$ are fixed and the sentence is the input.

## Depends on

- [Presburger arithmetic with scalar multiplications](presburger-arithmetic-with-scalar-multiplication.md)
- [Field](../../../../Algebra/rings-and-fields/field.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof follows Hieronymi and Tychonievich. Using the Ostrowski representations of natural numbers with respect to the continued fractions of $\alpha$ and of $\beta$, one defines in $\mathbb Q(\alpha, \beta)$-PA, with few quantifier alternations, an $\exists^*\forall^*$-definable relation $\mathrm{Member}$, built from the interaction of the two Ostrowski representations, which is used to code the successive configurations of a computation. With it, for a fixed universal Turing machine $U$ and an input $x$, one writes an $\exists^*\forall^*\exists^*\forall^*$ sentence $\varphi_x$ asserting the existence of a halting computation of $U$ on $x$; $\varphi_x$ is true iff $U$ halts on $x$. Counting the occurrences of $\mathrm{Member}$ (at most $200$) and its quantifiers bounds each block by $k = 20000$ variables (Section 7, proof of Theorem 7.1).

## Sources

- P. Hieronymi, D. Nguyen and I. Pak, "Presburger Arithmetic with algebraic scalar multiplications", *Logical Methods in Computer Science* 17(3), 2021, article 4, pp. 4:1–4:34, <https://doi.org/10.46298/lmcs-17(3:4)2021>; numbers from arXiv:1805.03624v7, <https://arxiv.org/abs/1805.03624v7>: Section 7: definition (7.1), Theorem 7.1 and its proof (Lemma 7.12 and the final construction of $\varphi_x$).
