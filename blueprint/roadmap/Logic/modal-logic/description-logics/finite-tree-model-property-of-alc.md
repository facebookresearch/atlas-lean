# Finite tree model property of ALC

Every ALC concept $C_0$ that is satisfiable with respect to the empty TBox, in the sense of [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md), is satisfiable in a finite interpretation that has the shape of a tree whose root belongs to $C_0^{\mathcal I}$: the domain and the union of the role relations form a finite tree, whose depth is bounded linearly by the size of $C_0$ and whose branching is bounded by the number of distinct existential restrictions in the negation normal form of $C_0$. (Counting in $C_0$ itself is not enough: $\neg\forall r.P$ has no existential restriction but needs an $r$-successor.)

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)

## Proof depends on

- [Correctness of the ALC tableau algorithm](correctness-of-the-alc-tableau-algorithm.md)

## Sources

- F. Baader and U. Sattler, "An overview of tableau algorithms for description logics", *Studia Logica* 69(1):5–40, 2001, <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSattler-StudiaLogica.pdf>, Section 3, the canonical interpretation and the finite tree model property, pp. 8–9.
