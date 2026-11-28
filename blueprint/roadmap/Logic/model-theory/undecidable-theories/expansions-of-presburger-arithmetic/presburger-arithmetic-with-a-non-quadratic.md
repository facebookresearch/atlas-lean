# Presburger arithmetic with a non-quadratic algebraic scalar is undecidable

For a real algebraic irrational $\alpha$ of degree at least three, the truth of $\alpha$-Presburger sentences is undecidable, already for sentences with four alternating quantifier blocks of $20000$ integer variables each.

**Theorem (Hieronymi, Nguyen and Pak).** Let $\alpha$ be a real algebraic irrational number that is not quadratic. There is no algorithm that decides, given an $\exists^k\forall^k\exists^k\forall^k$ [$\alpha$-PA sentence](presburger-arithmetic-with-scalar-multiplication.md) with $k = 20000$, whether it is true in $\mathbb Z$.

Here $\alpha$ is fixed and the sentence is the input. For quadratic irrational $\alpha$ the problem is decidable (Theorem 3.1 of the source), though deciding sentences with $r \ge 4$ alternating blocks requires space a tower of exponentials of height $r - 3$ (Theorem 1.3); whether three alternating blocks already give undecidability for non-quadratic $\alpha$ is left open (Conjecture 8.1).

## Depends on

- [Presburger arithmetic with scalar multiplications](presburger-arithmetic-with-scalar-multiplication.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Presburger arithmetic over Q(α, β) is undecidable](presburger-arithmetic-over-two-independent.md)

## Expansion

If $\alpha$ is algebraic and not quadratic, then $1, \alpha, \alpha^2$ are linearly independent over $\mathbb Q$, and $\mathbb Q(\alpha, \alpha^2) = \mathbb Q(\alpha)$. Applying the theorem for two independent scalars with $\beta = \alpha^2$, and clearing denominators so that all coefficients lie in $\mathbb Z[\alpha]$, gives the result. Undecidability of $\alpha$-PA for non-quadratic $\alpha$ also follows from the undecidability of the theory of $(\mathbb R, <, +, \mathbb Z, x \mapsto \alpha x)$ (Hieronymi and Tychonievich), with no bound on the number of quantifier alternations; the point here is the bound of four blocks.

## Sources

- P. Hieronymi, D. Nguyen and I. Pak, "Presburger Arithmetic with algebraic scalar multiplications", *Logical Methods in Computer Science* 17(3), 2021, article 4, pp. 4:1–4:34, <https://doi.org/10.46298/lmcs-17(3:4)2021>; numbers from arXiv:1805.03624v7, <https://arxiv.org/abs/1805.03624v7>: Theorem 1.5 (deduced from Theorem 7.1 in Section 7), Theorem 1.3, Theorem 3.1 and Conjecture 8.1.
- P. Hieronymi and M. A. Tychonievich, "Interpreting the projective hierarchy in expansions of the real line", *Proceedings of the American Mathematical Society* 142(9):3259–3267, 2014, <https://doi.org/10.1090/S0002-9939-2014-12023-5>: undecidability of the expansion of the real line used as a starting point; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Section 1.2).
