# Gap theorem for the proof complexity of constraint satisfaction problems

For every finite constraint language $B$, either all unsatisfiable instances of $\mathrm{CSP}(B)$ have constant-width resolution refutations, or they admit no subexponential bounded-depth Frege, no sublinear-degree real Polynomial Calculus, and no sublinear-degree Sums-of-Squares refutations; the dividing line is bounded width.

A finite relational structure $B$ (the constraint language) defines $\mathrm{CSP}(B)$: given a finite structure $A$ over the same vocabulary, decide whether there is a homomorphism $A \to B$. $B$ has **width** $k$ if Spoiler wins the existential $k$-pebble game on $A$ and $B$ whenever there is no homomorphism from $A$ to $B$, and **bounded width** if it has width $k$ for some $k$. A statement that $B$ has efficient refutations in a proof system $P$ means that, for some and hence every local encoding of the instances as CNF formulas or polynomial systems, all unsatisfiable instances of $\mathrm{CSP}(B)$ have efficient $P$-refutations; sublinear means $o(n)$, sublinear-exponential $2^{o(n)}$ and subexponential $2^{n^{o(1)}}$, with $n$ the number of variables.

**Theorem.** Let $B$ be a finite constraint language. Exactly one of the following holds:

1. $B$ has resolution refutations of constant width;
2. $B$ has neither bounded-depth Frege refutations of subexponential size, nor Polynomial Calculus refutations over the reals of sublinear degree, nor Sums-of-Squares refutations of sublinear degree.

Case 1 happens exactly when $B$ has bounded width. Consequently the following are equivalent: $B$ has bounded width; constant-width resolution refutations; sublinear-width resolution refutations; polynomial-size resolution refutations; sublinear-exponential-size resolution refutations; bounded-depth polynomial-size Frege refutations; bounded-depth subexponential-size Frege refutations; constant-degree SA, SOS and real PC refutations; sublinear-degree SA, SOS and real PC refutations.

## Proof sketch

The key ingredient is closure under reductions: the classes of constraint languages with efficient refutations in bounded-depth Frege, in algebraic systems and in semialgebraic systems are closed under pp-interpretations, homomorphic equivalence and adding constants. By the algebraic characterization of unbounded width of Barto-Kozik and Bulatov, a language without bounded width reduces, through these operations, from systems of linear equations over a nontrivial finite Abelian group, and the known lower bounds for such systems (via Ben-Sasson's bounded-depth Frege results, Buss-Grigoriev-Impagliazzo-Pitassi for polynomial calculus and Chan for SOS) transfer to $\mathrm{CSP}(B)$. Bounded width gives constant-width resolution through the correspondence between local consistency, existential pebble games and resolution width. Lovász-Schrijver is not covered by the dichotomy: bounded-degree LS refutes linear equations over $\mathbb{Z}_2$.

## Depends on

- [Sherali-Adams proof system](sherali-adams-proof-system.md)
- [Polynomial calculus](../polynomial-calculus.md)
- [Sums-of-Squares proof system](../sums-of-squares-proof-system.md)
- [CNF formula](../../../propositional-logic/conjunctive-normal-form/cnf.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Width of a derivation](../../../propositional-logic/resolution-size-and-width/derivation-width.md)

## Proof depends on

None.

## Sources

- Albert Atserias, Joanna Ochremiak, "Proof complexity meets algebra", *ACM Transactions on Computational Logic* 20(1), 2019, https://doi.org/10.1145/3265985; numbering of arXiv:1711.07320v2 (Theorem 1, Corollary 1, Sections 2.5, 4, 5 and 6).
