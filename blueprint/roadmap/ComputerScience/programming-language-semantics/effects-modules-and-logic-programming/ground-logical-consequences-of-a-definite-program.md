# Ground logical consequences of a definite program

Let $P$ be a definite logic program, a set of clauses $A_0 \leftarrow A_1, \dots, A_n$ ($n \ge 0$) of atoms over a first-order signature, each read as its universal closure, and let $B_P$ be the Herbrand base, the set of ground atoms over the signature. An atom is a predicate symbol applied to terms, $p(t_1, \dots, t_k)$; there is no built-in equality, so equations $s = t$ are not atoms. A [Herbrand model](is-model.md) of $P$ is a set of ground atoms that is a Herbrand model of the set of ground instances of the clauses of $P$, and $M_P$ is the [least Herbrand model](least-model.md) of that set. A ground atom $A$ is a logical consequence of $P$, written $P \models A$, if $A$ is true in every model of $P$, every first-order structure in which all clauses of $P$ are true.

1. If a ground atom $A$ lies in every Herbrand model of $P$, then $P \models A$. In particular, every atom of $M_P$ is a logical consequence of $P$.
2. If the signature has at least one constant symbol, then $M_P = \{A \in B_P : P \models A\}$.

## Proof sketch

Let $\mathcal{I}$ be a model of $P$. Every ground instance of a clause of $P$ is true in $\mathcal{I}$, so the set $\{A \in B_P : \mathcal{I} \models A\}$ is a Herbrand model of $P$. If $A$ lies in every Herbrand model of $P$, it lies in this one, so $\mathcal{I} \models A$; this proves part 1. For part 2, part 1 gives the inclusion $\subseteq$. Conversely, with a constant symbol the set of ground terms is nonempty, and the structure on it in which each ground term denotes itself and the true atoms are those of $M_P$ is a model of $P$, because $M_P$ is a Herbrand model of every ground instance. So every ground atom $A$ with $P \models A$ lies in $M_P$.

## Remarks

- Part 1 extends to existentially quantified conjunctions of atoms, but not to arbitrary formulas. Over the signature with one constant $a$ and one unary predicate $p$, every Herbrand model of $P = \{p(a)\}$ satisfies $\forall x\, p(x)$, while the structure with universe $\{0, 1\}$, $a$ interpreted as $0$ and $p$ as $\{0\}$ is a model of $P$ in which $\forall x\, p(x)$ is false.
- Part 2 needs the constant symbol. Over a signature with a unary function symbol, a unary predicate $q$, a nullary predicate $p$ and no constant, the program $q(x) \leftarrow$, $p \leftarrow q(x)$ has no ground instances, so $M_P$ is empty, yet $P \models p$, since first-order structures have nonempty universes.

## Depends on

- [Least Herbrand model](least-model.md)
- [Herbrand model of a set of ground definite clauses](is-model.md)

## Proof depends on

- [Least Herbrand model of a definite logic program](least-herbrand-model-of-a-definite-logic-program.md)
- [Term-generated models of ground instances](../../../Logic/first-order-logic/superposition/term-generated-models-of-ground-instances.md)

## Sources

- *Definite programs*, lecture handout for CSE 505, 29 October 2008, copy hosted at Radboud University Nijmegen, <http://www.cs.ru.nl/~herman/onderwijs/soflp2013/defpgms-handout.pdf>: definite clauses over atomic formulas $p(t_1, \dots, t_n)$, a predicate symbol applied to terms (slide 2), the properties of Herbrand models (slide 9, items 3 and 4; item 3 is stated there for any formula $F$, see Remarks), the sufficiency of Herbrand models (slide 10) and $M_P$ as the set of ground logical consequences (slide 13).
- H. Strass (based on slides by M. Thielscher), *Least Herbrand Models*, Lecture 5 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/8/8b/FLP2026-05.pdf>: Theorem 4.30 (for every ground atom $A$, $P \models A$ if and only if $M(P) \Vdash A$) and Theorem 4.29 ($M(P)$ is the least Herbrand model of $P$).
- M. H. van Emden and R. A. Kowalski, The semantics of predicate logic as a programming language, *J. ACM* 23(4) (1976), 733–742: clauses over atomic formulas $P(t_1, \dots, t_m)$, a predicate symbol applied to terms (Section 2), the assumption of a constant symbol (Section 4), and a ground atom is logically implied by a set of clauses if and only if it lies in every Herbrand model (Section 5).
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987.
