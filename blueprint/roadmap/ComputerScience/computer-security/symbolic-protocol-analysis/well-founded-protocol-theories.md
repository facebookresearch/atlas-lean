# Well-founded protocol theories

In [multiset rewriting](multiset-rewriting-with-existential-quantification.md), a rule $l \to r$ *enables* a rule $l' \to r'$ if some fact in $\sigma r$ is also in $\sigma' l'$ for some substitutions
$\sigma, \sigma'$, and a theory $T$ *precedes* a theory $S$ if no rule of $S$ enables a rule of $T$.

- A theory $A$ is a *bounded role theory* if there is a finite list of *role-state* predicates $S_0, S_1, \dots, S_k$ such that every rule $l \to r$ of $A$ has exactly one
  role-state predicate $S_i$ in $l$ and exactly one $S_j$ in $r$, with $i < j$; $S_0$ is the *initial* role state.
- For bounded role theories $A_1, \dots, A_k$, a *role generation theory* is a set of rules $P(\vec s), Q(\vec t), \dots \to S_i(\vec r), P(\vec s), Q(\vec t), \dots$, where the left side is a finite list of
  persistent facts with no role states and $S_i$ is the initial role state of one of the $A_i$.
- A subtheory $S \subseteq T$ is *bounded* if every formula on the right of its rules contains existentials or is persistent in $T$.
- A *well-founded protocol theory* is a union $P = I \cup R \cup A_1 \cup \dots \cup A_n$ of a bounded subtheory $I$ (the initialization theory) with no role states, a role
  generation theory $R$ involving only facts created by $I$ and the initial role states of the $A_i$, and bounded role theories $A_1, \dots, A_n$ with pairwise disjoint
  role-state predicates, such that $I$ precedes $R$ and $R$ precedes each $A_i$.

## Depends on

- [Multiset rewriting with existential quantification](multiset-rewriting-with-existential-quantification.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 3.1, Definitions 3.1–3.5.
