# Least Herbrand model of a definite logic program

Let $P$ be a definite logic program, a finite set of clauses $A_0 \leftarrow A_1, \dots, A_n$ ($n \ge 0$) of atoms, and let $B_P$ be its Herbrand base, the set of ground atoms over the signature of $P$.

1. **Least model.** The intersection of any nonempty family of Herbrand models of $P$ is a Herbrand model of $P$. Hence $P$ has a unique least Herbrand model $M_P$, contained in every Herbrand model of $P$.
2. **Logical consequences.** If a ground atom $A$ is true in every Herbrand model of $P$, then $P \models A$ (this extends to existentially quantified conjunctions of atoms, but not to arbitrary formulas: for $P = \{p(a)\}$ every Herbrand model satisfies $\forall x\, p(x)$). Consequently $M_P$ is exactly the set of ground atoms that are logical consequences of $P$.
3. **Fixed-point characterization.** The immediate consequence operator $T_P : 2^{B_P} \to 2^{B_P}$ maps $I$ to the set of $A_0$ such that $A_0 \leftarrow A_1, \dots, A_n$ is a ground instance of a clause of $P$ with $A_1, \dots, A_n \in I$. Then $M_P = T_P \uparrow \omega = \bigcup_{i \ge 0} T_P^i(\emptyset)$, and this is the least fixed point of $T_P$.

**Proof of part 3.** $T_P$ is monotone. Every Herbrand model $M$ of $P$ satisfies $T_P(M) \subseteq M$, so by induction $T_P^i(\emptyset) \subseteq M_P$ for every $i$. Conversely, $T_P \uparrow \omega$ satisfies every ground instance of every clause, because the finitely many body atoms of an instance all appear in some $T_P^i(\emptyset)$. So $T_P\uparrow\omega$ is a Herbrand model, and $M_P \subseteq T_P \uparrow \omega$. The same finiteness argument shows that $T_P \uparrow \omega$ is a fixed point, and every fixed point contains all $T_P^i(\emptyset)$.

## Sources

- *Definite programs*, lecture handout for CSE 505, 29 October 2008, copy hosted at Radboud University Nijmegen, <http://www.cs.ru.nl/~herman/onderwijs/soflp2013/defpgms-handout.pdf>: the properties of Herbrand models (items 1–4: closure under intersection, the unique least model $M_P$, logical consequence from Herbrand models, $M_P$ as the ground logical consequences) and the immediate consequence operator with $T_P^i(\emptyset) \subseteq M_P \subseteq T_P \uparrow \omega$.
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987.
