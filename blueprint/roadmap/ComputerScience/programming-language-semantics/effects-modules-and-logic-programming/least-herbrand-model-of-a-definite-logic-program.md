# Least Herbrand model of a definite logic program

Let $B$ be a set of ground atoms and $P$ a set of ground definite clauses $A_0 \leftarrow A_1, \dots, A_n$ ($n \ge 0$) with $A_0, \dots, A_n \in B$, such as the set of ground instances of the clauses of a definite logic program over its Herbrand base $B$. A Herbrand interpretation is a set $I \subseteq B$ of ground atoms, those taken to be true. It is a Herbrand model of $P$ if $A_0 \in I$ for every clause $A_0 \leftarrow A_1, \dots, A_n$ of $P$ with $A_1, \dots, A_n \in I$. Let $M_P$ be the intersection of all Herbrand models of $P$, and let the immediate consequence operator $T_P : 2^B \to 2^B$ map $I$ to the set of heads $A_0$ of the clauses $A_0 \leftarrow A_1, \dots, A_n$ of $P$ with $A_1, \dots, A_n \in I$.

1. **Least model.** The intersection of any family of Herbrand models of $P$ is a Herbrand model of $P$. Hence $M_P$ is a Herbrand model of $P$ contained in every Herbrand model of $P$: it is the unique least Herbrand model of $P$.
2. **Fixed-point characterization.** $M_P$ is the least fixed point of $T_P$, and $M_P = T_P \uparrow \omega = \bigcup_{i \ge 0} T_P^i(\emptyset)$.

## Proof

**Proof of part 2.** $T_P$ is monotone. Every Herbrand model $M$ of $P$ satisfies $T_P(M) \subseteq M$, so by induction $T_P^i(\emptyset) \subseteq M_P$ for every $i$. Conversely, $T_P \uparrow \omega$ satisfies every clause of $P$, because the finitely many body atoms of a clause all appear in some $T_P^i(\emptyset)$. So $T_P\uparrow\omega$ is a Herbrand model, and $M_P \subseteq T_P \uparrow \omega$. The same finiteness argument shows that $T_P \uparrow \omega$ is a fixed point, and every fixed point contains all $T_P^i(\emptyset)$.

## Remarks

- For a definite logic program $P$ with variables, a Herbrand interpretation is a model of $P$ exactly when it is a model of the set of ground instances of the clauses of $P$, so the least Herbrand model and the immediate consequence operator of $P$ are those of that set.
- Strass, and van Emden and Kowalski, state the model intersection property for a nonempty family. The empty family has intersection $B$, which is a Herbrand model of every set of clauses over $B$.
- When the atoms are predicate symbols applied to terms, with no built-in equality, and the signature has a constant symbol, $M_P$ is exactly the set of ground atoms that are logical consequences of $P$; without a constant symbol, every atom of $M_P$ is still a logical consequence of $P$ ([Ground logical consequences of a definite program](ground-logical-consequences-of-a-definite-program.md)).

## Sources

- *Definite programs*, lecture handout for CSE 505, 29 October 2008, copy hosted at Radboud University Nijmegen, <http://www.cs.ru.nl/~herman/onderwijs/soflp2013/defpgms-handout.pdf>: the properties of Herbrand models (slide 9, items 1 and 2: closure under intersection and the unique least model $M_P$) and the immediate consequence operator with $T_P^i(\emptyset) \subseteq M_P \subseteq T_P \uparrow \omega$ (slide 14).
- H. Strass (based on slides by M. Thielscher), *Least Herbrand Models*, Lecture 5 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/8/8b/FLP2026-05.pdf>: Lemma 4.26 (Herbrand models of a program are those of its ground instances), the model intersection property and its corollary (slide 6), Lemma 4.32 (models are the pre-fixpoints of $T_P$), Lemma 4.33 ($T_P$ is order-preserving and finitary), Theorem 4.22 (Kleene's fixpoint theorem), Proposition 4.23 and Theorem 4.34.
- M. H. van Emden and R. A. Kowalski, The semantics of predicate logic as a programming language, *J. ACM* 23(4) (1976), 733–742: the model-intersection property (Section 5), the immediate consequence operator $T$ (Section 6), the theorem that a Herbrand interpretation $I$ is a model if and only if $T(I) \subseteq I$, with its corollary (Section 7), and $\bigcup_m T^m(\emptyset) = \bigcap M(A)$ (Section 8).
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987.
