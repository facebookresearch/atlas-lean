# Zeros of integer polynomials at powers of two are decidable

This result proves the proposition stated as [Decidability of zeros of integer polynomials at powers of two](powers-of-two-zeros-decidable.md). Precisely, it is decidable, given a polynomial $P \in \mathbb{Z}[x_1, \dots, x_m]$, whether there are $n_1, \dots, n_m \in \mathbb{N}$ with $P(2^{n_1}, \dots, 2^{n_m}) = 0$. Precisely, the set of list-of-monomials encodings of integer polynomials that have a zero at powers of two is a computable set. The question is related to the Mordell-Lang conjecture for tori.

## Sources

- B. Poonen and T. Scanlon (moderators), notes by J. Demeyer, AIM workshop Extensions of Hilbert's tenth problem, problem list, Question 8 (T. Pheidas), https://web.archive.org/web/20250808061106/https://aimath.org/WWN/hilberts10th/hilberts10th.pdf.
- J. Avigad and Y. Yin, "Quantifier elimination for the reals with a predicate for the powers of two", Theoretical Computer Science 370 (2007), 48-59, https://doi.org/10.1016/j.tcs.2006.10.005: a decision procedure for the reals with a predicate $A$ for the integer powers of two, which applies to $\exists x_1 \cdots \exists x_m\, (P(x) = 0 \wedge \bigwedge_i (A(x_i) \wedge x_i \ge 1))$, the bound $x_i \ge 1$ selecting exactly the natural exponents.
