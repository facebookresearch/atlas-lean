# First-order queries over unary conjunctive views

A first-order unary-conjunctive-view (UCV) query is a first-order formula whose atoms are unary views, each defined by a conjunctive query with one free variable. The views may not be used as relations of a richer signature: only Boolean combinations and quantifications of view atoms are allowed.

**Views.** Fix a relational vocabulary $\sigma$. A *unary conjunctive view* over $\sigma$ is a rule

$$
V(y) \leftarrow R_1(u_1), \dots, R_k(u_k)
$$

with $R_i \in \sigma$, free tuples $u_i$ of matching arity, and head variable $y$ among the variables of the body; on a $\sigma$-structure $\mathbf{A}$ it defines the set of elements $a$ such that $\exists \bar{x}\, (R_1(u_1) \wedge \dots \wedge R_k(u_k))$ holds with $y \mapsto a$, the other variables $\bar{x}$ being existentially quantified. Unless stated otherwise the body contains neither equality nor negation.

**Definition (Bailey, Dong and To).** For a finite set $\mathcal{V}$ of unary conjunctive views over $\sigma$, the set $\mathrm{UCV}(\sigma, \mathcal{V})$ is the least set of formulas such that $V(x) \in \mathrm{UCV}(\sigma, \mathcal{V})$ for every $V \in \mathcal{V}$ and variable $x$, and that is closed under $\neg$, $\wedge$ and $\exists x$. A formula is *satisfiable* if some $\sigma$-structure, finite or infinite, makes it true for some assignment, and *finitely satisfiable* if some finite structure does.

Three extensions change the view bodies but keep the same first-order layer over the views:

- *unary conjunctive$^{\neq}$ views* allow inequality atoms $x \neq y$ in the body;
- *unary conjunctive$^{\neg}$ views* allow negated atoms in the body;
- *unary conjunctive$^{\mathrm{rec}}$ views* allow a view to be defined by several rules, possibly recursive, read as least fixed points.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

None.

## Expansion

UCV queries strictly contain the monadic first-order class without equality, because the views may be defined over relations of any arity. Allowing a view body to be any existential positive formula with one free variable adds no expressive power: the body can be put in disjunctive normal form and split into several conjunctive views. Satisfiability of UCV queries, over finite and over arbitrary structures, is decidable, while each of the extensions above makes it undecidable, so the class is maximal in this sense.

## Sources

- James Bailey, Guozhu Dong and Anthony Widjaja To, "Logical Queries over Views: Decidability and Expressiveness", ACM Transactions on Computational Logic 11(2), pp. 1–35, 2010, <https://doi.org/10.1145/1656242.1656243>; Sections 2.1, 2.2, 3 and 5 of arXiv:0803.2559v1 (the copy read), <https://arxiv.org/abs/0803.2559v1>.
