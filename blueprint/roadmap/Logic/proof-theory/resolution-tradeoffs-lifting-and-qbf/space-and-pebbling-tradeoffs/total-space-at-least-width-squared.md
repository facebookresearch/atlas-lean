# Total space in resolution is at least width squared

For every unsatisfiable $k$-CNF formula whose minimum refutation width $W$ is at least $k + 4$, every resolution refutation must at some point hold clauses with at least $(W - k - 4)^2 / 16$ literal occurrences in total.

**Theorem.** Let $\varphi$ be an unsatisfiable $k$-CNF formula with $\mathit{width}(\varphi \vdash \bot) \ge k + 4$. Then

$$
\mathit{TotSp}(\varphi \vdash \bot) \ge \frac{1}{16} \bigl(\mathit{width}(\varphi \vdash \bot) - k - 4\bigr)^2 .
$$

Equivalently, every unsatisfiable $k$-CNF formula satisfies $\mathit{TotSp}(\varphi \vdash \bot) \ge \max\bigl(0, \mathit{width}(\varphi \vdash \bot) - k - 4\bigr)^2 / 16$. The source prints the squared bound without the hypothesis $\mathit{width}(\varphi \vdash \bot) \ge k + 4$, and it fails without it: the clauses $x$, $\neg x$ and $a_1 \lor \dots \lor a_{10}$ form an unsatisfiable $10$-CNF with refutation width $1$ and total space at most $2$, below $(1 - 10 - 4)^2/16$. The last step of the source's proof, with $\mathit{awidth}(\varphi \vdash \bot) = r + 1$ (asymmetric width, defined below), squares $(r - 1)/2 \ge (\mathit{width}(\varphi \vdash \bot) - k - 4)/2$, which needs the right side to be nonnegative.

The proof gives more: every resolution refutation of an unsatisfiable CNF $\varphi$ passes through a memory configuration containing at least $\frac{1}{2}(\mathit{awidth}(\varphi \vdash \bot) - 2)$ clauses, each of width at least $\frac{1}{2}(\mathit{awidth}(\varphi \vdash \bot) - 2)$, where $\mathit{awidth}$ is the asymmetric width.

The **asymmetric width** of a derivation $\pi = (C_1, \dots, C_\ell)$ with a witness function $\sigma$ (recording for each $C_i$ the indices of its premises, or that it is an axiom) assigns $0$ to axioms and to an inferred clause the width of its smaller premise; $\mathit{awidth}(\pi)$ minimizes over $\sigma$ the maximum of these values, and $\mathit{awidth}(\varphi \vdash \bot)$ minimizes over refutations. For an unsatisfiable $k$-CNF, $\mathit{width}(\varphi \vdash \bot) \le \mathit{awidth}(\varphi \vdash \bot) + \max\{\mathit{awidth}(\varphi \vdash \bot), k\}$.

## Expansion

This is the total-space analogue of the inequality $\mathit{CSp}(\varphi \vdash \bot) \ge \mathit{width}(\varphi \vdash \bot) - k + 1$ of Atserias and Dalmau. Given a refutation, locate a configuration in which some small clause appears and show that before that moment some configuration contained many wide clauses. The wide clauses are found with a family of partial assignments with a consistency and extension property, the one in a known characterization of asymmetric width (restated as Theorem 5), and the bound in terms of width follows from the comparison of width with asymmetric width. As a corollary, formulas with polynomial-size refutations but width $\omega(\sqrt{n})$ would need superlinear total space.

## Depends on

- [Variable space and total space of resolution refutations](variable-and-total-space.md)
- [Width of a derivation](../../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

None.

## Sources

- I. Bonacina, "Total space in resolution is at least width squared", *ICALP 2016*, LIPIcs 55, 56:1-56:13, doi:10.4230/LIPIcs.ICALP.2016.56 (Theorem 1, Theorem 2, Theorem 5 and Section 3).
