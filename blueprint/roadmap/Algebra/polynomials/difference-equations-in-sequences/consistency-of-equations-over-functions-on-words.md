# Consistency of equations over functions on words is undecidable

Over a field of characteristic zero, no algorithm decides whether a finite system of equations for functions on the words of a two-letter alphabet, with coefficients in a computable subfield, has a solution.

**Theorem (Pogudin–Scanlon–Wibmer).** Let $k$ be a field of characteristic zero, let $k_0 \subseteq k$ be a computable subfield, and let $M_2$ be the free monoid on two generators. There is no algorithm that decides, given a finite set $F$ of $M_2$-polynomials in finitely many unknowns with coefficients in $k_0$, whether the system $F = 0$ has a solution in $k^{M_2}$.

Conventions: $k^{M_2}$ is the ring of functions $x \colon M_2 \to k$, with $\sigma^w(x)(u) = x(uw)$ for words $u, w$, as in the linked definitions.

## Depends on

- [Difference rings and rings of sequences](difference-rings-and-equations-in-sequences.md)
- [Difference polynomials and their solutions](difference-polynomials-and-their-solutions.md)
- [Computable subfields](computable-subfields.md)
- [Field](../../rings-and-fields/field.md)
- [Predicates decidable by a single-tape Turing machine](../../../TheoryOfComputation/turing-machines/single-tape/decidable-and-recognizable-predicates-on-single/single-tape-decidable.md)

## Proof depends on

- [Radical difference ideal membership is undecidable](radical-difference-ideal-membership.md)

## Expansion

The proof reduces clause 2 of the linked result (a system $f_1 = \dots = f_\ell = 0$, $g \ne 0$ of difference equations over $\mathbb{N}$) to a system over $M_2$ with generators $a, b$. After adding unknowns one may assume that $g \in k_0[\boldsymbol{X}]$ and $f_1, \dots, f_\ell \in k_0[\boldsymbol{X}, \sigma(\boldsymbol{X})]$. Replace every $\sigma$ by $\sigma^a$ and every $X_i$ by a new unknown $Y_i$, giving $\tilde f_1, \dots, \tilde f_\ell, \tilde g$, and take

$$
F = \{\tilde f_1, \dots, \tilde f_\ell,\ Z \sigma^b(\tilde g) - 1\}.
$$

From a solution of $F = 0$ in $k^{M_2}$, the sequence $(\mathbf{y}_{b a^i})_{i \in \mathbb{N}}$ solves $f_1 = \dots = f_\ell = 0$, and $Z \sigma^b(\tilde g) = 1$ gives $g(\mathbf{y}_b) \ne 0$. Conversely, given a solution $(\mathbf{x}_i)_{i \in \mathbb{N}}$ with $g \ne 0$, shifted so that $c = g(\mathbf{x}_0) \ne 0$, put $\mathbf{y}_m = \mathbf{x}_{A(m)}$, where $A(m)$ is the number of trailing letters $a$ of the word $m$, and $z_m = c^{-1}$; then $A(ma) = A(m) + 1$ and $A(mb) = 0$ give a solution of $F = 0$. All steps are proved in the source from the linked result.

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; Proposition 3.10 of arXiv:1909.03239v2, proved in Section 4.5 there by reduction to Corollary 3.8.
