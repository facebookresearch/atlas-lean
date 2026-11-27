# The Atserias–Müller reduction from SAT to resolution proof size

There are constants $c, d > 0$ and a polynomial-time map $G$ from $3$-CNF formulas to CNF formulas with the following property. For a $3$-CNF formula $F$ write $r$ for the size of $G(F)$ and $s$ for the length of a shortest resolution refutation of $G(F)$, with $s = \infty$ when $G(F)$ is satisfiable. Then:

- if $F$ is satisfiable, then $s < r^{c}$ (in particular $G(F)$ is unsatisfiable);
- if $F$ is unsatisfiable, then $s > 2^{r^{1/d}}$.

There is no promise that $G(F)$ is unsatisfiable on the second side: it may be satisfiable, with $s = \infty$. The constants $c$ and $d$ can be chosen arbitrarily close to $1$ and $2$. For $F$ on $n$ variables, $G(F) = \mathrm{RREF}(F, 13n^2)$, the relativization (in the style of Dantchev and Riis, with a built-in linear order on the indices) of the formula $\mathrm{REF}(F, t)$ whose satisfying assignments are exactly the resolution refutations of $F$ of length $t$.

## Proof sketch

If $F$ has a satisfying assignment $\alpha$, resolution derives, for each index $u = 1, 2, \dots$ in order, a clause stating that line $u$ of the purported refutation contains a literal true under $\alpha$; at the final line, which must be the empty clause, this is a contradiction. The refutation has length $O((tnm)^2)$ for $m$ clauses.

If $F$ is unsatisfiable, the lower bound goes through **index-width**, the number of line indices a clause mentions. Every clause of $\mathrm{REF}(F, t)$ has index-width at most $2$, and for $2^n \ge t \ge 6nw$ every resolution refutation of $\mathrm{REF}(F, t)$ has index-width at least $w$: below that width, refutations cannot tell $\mathrm{REF}(F, t)$ from $\mathrm{REF}(F, 2^{n+1} - 1)$, which is satisfied by the full-tree refutation of $F$. A random restriction keeps each index of $\mathrm{RREF}(F, 13nw)$ independently with probability $1/2$ and sets the variables of the discarded indices at random. A clause of index-width at least $w$ survives with probability at most $(3/4)^{w}$, so a refutation of length at most $2^{2w/5}$ restricts, for some outcome, to a refutation of a copy of $\mathrm{REF}(F, A)$ with $|A| \ge 6nw$ and index-width below $w$, which is impossible. Taking $w = n$ gives the bound.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Sources

- A. Atserias, M. Müller, "Automating resolution is NP-hard", FOCS (2019); Journal of the ACM 67 (2020), arXiv:1904.02991 (Theorem 2, Lemmas 4, 10 and 11).
