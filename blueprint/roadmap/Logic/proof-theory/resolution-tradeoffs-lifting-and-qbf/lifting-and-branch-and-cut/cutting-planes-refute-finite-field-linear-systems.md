# Cutting planes refute unsatisfiable linear systems over finite fields in quasi-polynomial size

Every unsatisfiable system of $m$ linear equations over a finite field, encoded as a CNF formula $F$, has a cutting planes refutation of size $|F|^{O(\log m)}$, generalizing quasi-polynomial cutting planes refutations of Tseitin formulas.

**Theorem.** Let $F$ be the CNF encoding of an unsatisfiable system of $m$ linear equations over a finite field. Then there is a cutting planes refutation of $F$ of size $|F|^{O(\log m)}$.

Here a width-$d$ equation over $\mathbb{F}_q$ is encoded by $q^{d-1}$ width-$d$ clauses, one ruling out each falsifying assignment, and for a width-$d$ system of $m$ equations $|F| := m q^{d-1}$. The underlying stabbing planes refutation has size $(mqd)^{O(\log m)} q^d = |F|^{O(\log m)}$.

## Expansion

The stabbing planes refutation keeps a set $I \subseteq [m]$ of equations that must contain one violated by the queries made so far. It splits $I$ into halves $I_1, I_2$ of roughly equal size and branches on all values of the linear forms $\sum_{i \in I_1} f_i$ and $\sum_{i \in I_2} f_i$; by unsatisfiability one half is inconsistent with the queried values, and the refutation recurses on it, so the depth is $O(\log m)$. Over $\mathbb{F}_2$ this is the branch decomposition procedure behind the quasi-polynomial stabbing planes refutations of Tseitin formulas. These refutations are facelike, so the characterization of cutting planes as facelike stabbing planes converts them into cutting planes refutations. This contrasts with systems of linear equations over the reals, for which Filmus, Hrubeš and Lauria proved that cutting planes needs exponential size.

## Depends on

None.

## Proof depends on

- [Cutting planes equal facelike stabbing planes](cutting-planes-equal-facelike-stabbing-planes.md)
- [Dadush–Tiwari: cutting planes refute Tseitin formulas in quasi-polynomial size](../../stabbing-planes-and-semi-algebraic-branching/dadush-tiwari-cp-tseitin.md)

## Sources

- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", *CCC 2021*, LIPIcs 200, doi:10.4230/LIPIcs.CCC.2021.6, arXiv:2102.05019 (arXiv version read: the linear-equations theorem in Section 1, proved in Section 4 on refutations of linear equations over a finite field).
