# NP-hard propagation rules out GAC-preserving polynomial decompositions

If enforcing generalized arc consistency on a constraint type is NP-hard, then, unless P = NP, no uniformly constructible decomposition on which GAC can be enforced in polynomial time prunes as much as GAC on the constraints themselves.

Let $\mathcal C$ be a constraint type with encoded instances and a uniform polynomial-time evaluator. A **decomposition** of an instance $C$ is a set of constraints over $\mathrm{var}(C)$ and possibly additional variables with their own finite domains, whose solutions, projected onto $\mathrm{var}(C)$, are exactly the allowed tuples of $C$. A **decomposition scheme** for $\mathcal C$ maps each instance $C$ to a decomposition of $C$. The scheme is **GAC-poly-time** when there is one algorithm that, given $C$ and a domain $D_0$ on $\mathrm{var}(C)$, constructs the decomposition and enforces [generalized arc consistency](generalized-arc-consistency.md) on it (every constraint of the decomposition made GAC, to a common fixpoint, reporting failure if some domain empties) in time polynomial in the size of $C$ and $D_0$. It **achieves GAC on $C$** when, for every $D_0$, the domains it leaves on $\mathrm{var}(C)$ are exactly the GAC closure of $D_0$ for $C$, failure corresponding to the totally empty closure.

**Lemma.** Assume P $\ne$ NP. If GACDomain($\mathcal C$) is Turing-NP-hard (in particular, if NoGACWipeOut($\mathcal C$) is NP-hard), then no GAC-poly-time decomposition scheme for $\mathcal C$ achieves GAC on every instance of $\mathcal C$.

## Depends on

- [Generalized arc consistency](generalized-arc-consistency.md): GAC and the GAC closure.
- [Decision problems of generalized arc consistency](gac-reasoning-problems.md): the problems GACDomain and NoGACWipeOut, the encoding model, and Turing-NP-hardness and NP-hardness.
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md): the hypothesis P $\ne$ NP.
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md): the hypothesis P $\ne$ NP.

## Proof depends on

- [Intractability transfers between the GAC decision problems](gac-intractability-transfer.md): NP-hardness of NoGACWipeOut gives Turing-NP-hardness of GACDomain.

## Expansion

A GAC-poly-time scheme that achieved GAC on every instance would compute GACDomain$[C,D_0]$ in polynomial time; since every NP problem Turing-reduces to GACDomain, this would give P $=$ NP. Uniformity matters: a polynomial bound for propagating each decomposition, once someone hands it over, says nothing about constructing it.

The source applies the lemma to $\mathrm{Disjoint}([X_1,\dots,X_n],[Y_1,\dots,Y_m])$, requiring $X_i\ne Y_j$ for all $i,j$ (Theorem 4 of the cited version). Its natural decomposition into the binary constraints $X_i\ne Y_j$ is already arc consistent on $X_1,Y_1\in\{1,2\}$, $X_2,Y_2\in\{1,3\}$, $Y_3\in\{2,3\}$, while GAC on Disjoint removes $2$ from $X_1$, $3$ from $X_2$ and $1$ from $Y_1$ and $Y_2$: of the 32 assignments only $X_1=X_2=1$, $Y_1=2$, $Y_2=3$, $Y_3\in\{2,3\}$ are allowed (with $X_1=2$, $Y_1=1$ and $Y_3=3$ are forced and $X_2$ has no value left), so the GAC closure is $X_1=X_2=\{1\}$, $Y_1=\{2\}$, $Y_2=\{3\}$, $Y_3=\{2,3\}$. The source lists the removals from $X_2$, $Y_1$ and $Y_2$ but omits the removal of $2$ from $X_1$. Deciding whether Disjoint has an allowed tuple is NP-hard: with $X_i\in\{i,-i\}$ for the variables of a 3-CNF formula and $Y_j$ ranging over the three literals of clause $j$, an allowed tuple exists iff the formula is satisfiable (the $X_i$ take the false literals, the $Y_j$ a true literal of each clause). As a reduction from 3SAT on bitstrings, strings that do not decode to a CNF formula with at most three literals per clause go to the instance built from $x_1\wedge\neg x_1$ (no allowed tuple), and a formula without clauses goes to the instance built from $x_1$ (an allowed tuple exists). So every GAC-poly-time decomposition scheme for Disjoint is strictly weaker than GAC on Disjoint, unless P $=$ NP. The source proves the same consequence for AtMost1 on fixed-cardinality set variables (Theorem 5).

The source's notion of decomposition is informal; the definitions above make its one-line argument precise, adding the uniform construction that the argument needs. For polynomial-size CNF decompositions propagated by unit propagation, an unconditional limit for ALLDIFFERENT comes from monotone circuit lower bounds instead of P $\ne$ NP.

## Sources

- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. GAC-poly-time decompositions and Lemma 5 in §4.2, Theorem 4 (Disjoint) and Theorem 5 (AtMost1) of arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
