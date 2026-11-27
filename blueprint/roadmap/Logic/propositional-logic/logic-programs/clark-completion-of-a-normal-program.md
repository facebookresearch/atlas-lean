# Clark completion of a normal program

Let $P$ be a [finite ground normal logic program](normal-logic-program.md) over a finite set $A$ of atoms. For a rule $a \leftarrow b_1, \dots, b_m, \mathrm{not}\ c_1, \dots, \mathrm{not}\ c_n$ write its body as the formula $b_1 \wedge \dots \wedge b_m \wedge \neg c_1 \wedge \dots \wedge \neg c_n$. The *completion* of $P$ is the set of propositional formulas

$$a \leftrightarrow \bigvee_{\beta \in \mathrm{Bodies}(a)} \beta \qquad (a \in A),$$

where $\mathrm{Bodies}(a)$ is the set of bodies of the rules of $P$ with head $a$; an empty disjunction is false. For example, the completion of $p \leftarrow \mathrm{not}\ q$, $q \leftarrow \mathrm{not}\ r$ is $p \leftrightarrow \neg q$, $q \leftrightarrow \neg r$, $r \leftrightarrow \bot$. Every [model](models-of-a-normal-logic-program.md) of the completion is a model of $P$. The completion is due to K. L. Clark (1978).

## Depends on

- [Models of a normal logic program](models-of-a-normal-logic-program.md)
- [Normal logic program](normal-logic-program.md)

## Sources

- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Section 3.8: the completion $\Pi^{\mathrm{comp}}$ of a finite normal program and the example (49).
