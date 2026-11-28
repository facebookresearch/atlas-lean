# Models of a normal logic program

Let $P$ be a [finite ground normal logic program](normal-logic-program.md). An *interpretation* is a set $I$ of atoms, the atoms taken to be true. The body of a rule $a \leftarrow b_1, \dots, b_m, \mathrm{not}\ c_1, \dots, \mathrm{not}\ c_n$ is *true in* $I$ if $b_1, \dots, b_m \in I$ and $c_1, \dots, c_n \notin I$. The interpretation $I$ *satisfies* the rule if $a \in I$ whenever its body is true in $I$, that is, if $I$ is a model of the propositional formula $b_1 \wedge \dots \wedge b_m \wedge \neg c_1 \wedge \dots \wedge \neg c_n \to a$; and $I$ is a *model* of $P$ if it satisfies every rule of $P$. A model of $P$ is *minimal* if no proper subset of it is a model of $P$.

## Depends on

- [Normal logic program](normal-logic-program.md)

## Sources

- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Section 2 (interpretations as sets of atoms, truth of a clause body, models of a program, and Definition 2.4).
- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Section 3.8: the formula $\varphi(\mathit{Head} \leftarrow \mathit{Body})$ associated with a normal rule, and models of $\Pi^\varphi$.
