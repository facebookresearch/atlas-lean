# Containment of a conjunctive query in a Datalog query via the canonical database

Let $q(\bar x)$ be a conjunctive query and $(P, T)$ a Datalog query over the same extensional schema, both of arity $k$.
Freeze $q$ by a bijection $G$ from its variables to fresh constants that occur neither in $q$ nor in $P$, extended by the
identity on constants. Then $q \subseteq (P, T)$, that is, $q(D) \subseteq (P, T)(D)$ for every database $D$, if and only if

$$G(\bar x) \in (P, T)\bigl(G(A_q)\bigr),$$

where $A_q$ is the body of $q$. In particular containment of a conjunctive query in a Datalog query is decidable, by one
evaluation of $P$ on the frozen body of $q$.

## Depends on

- [Answers of a conjunctive query](../../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Datalog queries are preserved under homomorphisms](datalog-queries-are-preserved-under-homomorphisms.md)
- [A Datalog program has a minimum model containing its input](../fixpoint-semantics/a-datalog-program-has-a-minimum-model-containing-its-input.md)

## Sources

- S. Chaudhuri and M. Y. Vardi, "On the equivalence of recursive and nonrecursive Datalog programs", *J. Comput. System Sci.* 54(1) (1997) 61–78; conference version PODS 1992; author copy <https://www.cs.rice.edu/~vardi/papers/pods92rj.pdf>, Section 1 (p. 2 of the author copy): containment of a conjunctive query in a recursive program is decidable, citing earlier work.
- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Corollary 36.6 (homomorphism preservation, which gives the "if" direction) and Corollary 15.6 (the same freezing argument for conjunctive queries).
- M. Krötzsch, *Database Theory*, lecture notes, TU Dresden, Lecture 13, "Datalog Expressivity and Containment" (2 June 2025),
  slides 14–15 (a conjunctive query as the rule $\mathrm{Ans}(\bar x) \leftarrow Q$, and the containment test by freezing each
  variable to a fresh constant), <https://iccl.inf.tu-dresden.de/w/images/4/42/DBT2025-Lecture-13-print.pdf>.
