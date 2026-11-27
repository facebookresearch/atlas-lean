# Cutting planes refute unsatisfiable linear systems over finite fields in quasi-polynomial size

Every unsatisfiable system of $m$ linear equations over a finite field, encoded as a CNF formula $F$, has a cutting planes refutation of size $|F|^{O(\log m)}$, generalizing quasi-polynomial cutting planes refutations of Tseitin formulas.

**Theorem.** Let $F$ be the CNF encoding of an unsatisfiable system of $m$ linear equations over a finite field. Then there is a cutting planes refutation of $F$ of size $|F|^{O(\log m)}$.

Here $|F|$ is the size of the CNF encoding. A width-$d$ equation over $\mathbb{F}_q$ (one with $d$ nonzero coefficients) is satisfied by exactly $q^{d-1}$ of the $q^d$ assignments to its variables, since fixing $d-1$ of them determines the last, and falsified by the other $(q-1) q^{d-1}$. The encoding writes each field variable with Boolean variables and has one clause ruling out each falsifying assignment, so a width-$d$ system of $m$ equations gives at least $m (q-1) q^{d-1}$ clauses; for $q = 2$ these are exactly $2^{d-1}$ clauses of width $d$ per equation. The source counts $q^{d-1}$ clauses per equation, the number of satisfying assignments. The underlying stabbing planes refutation has size $(mqd)^{O(\log m)} q^d$, which is $|F|^{O(\log m)}$ because $m$, $q$, $d$ and $q^d$ are all at most $2|F|$.

## Expansion

The stabbing planes refutation keeps a set $I \subseteq [m]$ of equations that must contain one violated by the queries made so far. Fix coefficients $\alpha_i$ with $\sum_i \alpha_i f_i = 0$ but $\sum_i \alpha_i b_i \ne 0$ in $\mathbb{F}_q$, which exist by unsatisfiability. The refutation splits $I$ into halves $I_1, I_2$ of roughly equal size and branches on all values of the weighted sums $\sum_{i \in I_1} \alpha_i f_i$ and $\sum_{i \in I_2} \alpha_i f_i$; one half is inconsistent with the queried values, and the refutation recurses on it. The binary search takes $O(\log m)$ recursion rounds; each query is a tree over the possible values of a sum, and making these trees balanced gives a stabbing planes refutation of depth $O(\log^2(mqd))$. Over $\mathbb{F}_2$ this is the branch decomposition procedure behind the quasi-polynomial stabbing planes refutations of Tseitin formulas. These refutations are facelike, so the characterization of cutting planes as facelike stabbing planes converts them into cutting planes refutations. This contrasts with systems of linear equations over the reals, for which Filmus, Hrubeš and Lauria proved that cutting planes needs exponential size.

## Depends on

- [The stabbing planes proof system](../../stabbing-planes-and-semi-algebraic-branching/stabbing-planes-system.md)

## Proof depends on

- [Cutting planes equal facelike stabbing planes](cutting-planes-equal-facelike-stabbing-planes.md)

## Sources

- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", *CCC 2021*, LIPIcs 200, doi:10.4230/LIPIcs.CCC.2021.6, arXiv:2102.05019v2 (version read: the linear-equations theorem in Section 1, proved in Section 4 on refutations of linear equations over a finite field as Theorem 4.1, with Lemma 3.6; the depth $O(\log^2(mqd))$ is noted at the end of the proof of Theorem 4.1, and the count of $q^{d-1}$ clauses per equation printed before Theorem 4.1 is the number of satisfying assignments, corrected here).
