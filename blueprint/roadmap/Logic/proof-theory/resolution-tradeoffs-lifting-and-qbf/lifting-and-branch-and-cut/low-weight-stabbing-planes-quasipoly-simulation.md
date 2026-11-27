# Cutting planes quasi-polynomially simulates low-weight stabbing planes

A stabbing planes refutation of a CNF formula with size $s$ and coefficients bounded by $c$ yields a cutting planes refutation of size $s (cn)^{\log s}$; hence stabbing planes with quasi-polynomial coefficients needs size $2^{n^{\epsilon}}$ on some formulas.

**Theorem.** Let $F$ be an unsatisfiable CNF formula on $n$ variables with a stabbing planes refutation of size $s$ whose coefficients have magnitude at most $c$. Then $F$ has a cutting planes refutation of size $s (cn)^{\log s}$.

More generally, if a polytope $P \subseteq \mathbb{R}^n$ of diameter $d(P)$ has a stabbing planes refutation of size $s$ and maximum coefficient size $c$, then it has a facelike stabbing planes refutation of size $s (c \cdot d(P) \sqrt{n})^{\log s}$.

**Corollary.** Let $\mathrm{SP}^*$ be stabbing planes restricted to coefficients of magnitude $n^{\log^{O(1)} n}$. There is a family of unsatisfiable CNF formulas $F_n$ such that every $\mathrm{SP}^*$ refutation of $F_n$ has size at least $2^{n^\epsilon}$ for a constant $\epsilon > 0$. Moreover $\mathrm{SP}^*$ is not automatable unless $\mathrm{P} = \mathrm{NP}$.

## Expansion

Induct on $s$. At the root query $(ax \le b, ax \ge b + 1)$ assume the left subproof $\pi_L$ is the smaller one, $|\pi_L| \le s/2$. Replace the root by a path of queries $ax \le b_0 + i$ versus $ax \ge b_0 + i + 1$ for $i = 0, \dots, t - 1$, starting from the largest $b_0$ with $ax \ge b_0$ valid on $P$; each is facelike, and each slab $P \cap \{ax = b_0 + i\}$ is refuted by a copy of the facelike version of $\pi_L$. The slabs have width $1/\|a\|_2$, so $t \le d(P) \sqrt{n} \|a\|_\infty \le c\, d(P) \sqrt{n}$, and the recurrence $f(s) \le t f(s/2) + f(s_R)$ solves to the bound. A CNF polytope lies in $[0,1]^n$ of diameter $\sqrt{n}$, and facelike stabbing planes converts to cutting planes with polynomial overhead. The corollary combines this with known exponential cutting planes lower bounds and with NP-hardness of automating cutting planes.

## Depends on

- [The stabbing planes proof system](../../stabbing-planes-and-semi-algebraic-branching/stabbing-planes-system.md)

## Proof depends on

- [Cutting planes equal facelike stabbing planes](cutting-planes-equal-facelike-stabbing-planes.md)
- [Random logarithmic-width CNFs are hard for cutting planes](../../stabbing-planes-and-semi-algebraic-branching/random-cnf-cutting-planes.md)

## Sources

- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", *CCC 2021*, LIPIcs 200, doi:10.4230/LIPIcs.CCC.2021.6, arXiv:2102.05019 (arXiv version read: the quasi-polynomial simulation theorem and the $\mathrm{SP}^*$ lower bound in Section 1; the polytope version and the non-automatability corollary in Section 3.2).
