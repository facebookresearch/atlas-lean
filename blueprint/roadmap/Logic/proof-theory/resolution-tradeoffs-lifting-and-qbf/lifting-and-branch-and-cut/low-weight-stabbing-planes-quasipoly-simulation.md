# Cutting planes quasi-polynomially simulates low-weight stabbing planes

A stabbing planes refutation of a CNF formula with size $s$ and coefficients bounded by $c$ yields a cutting planes refutation of size $s (cn)^{\log s}$; hence stabbing planes with quasi-polynomial coefficients needs size $2^{n^{\epsilon}}$ on some formulas.

**Theorem.** Let $F$ be an unsatisfiable CNF formula on $n$ variables with a stabbing planes refutation of size $s$ whose coefficients have magnitude at most $c$. Then $F$ has a cutting planes refutation of size $s (cn)^{\log s}$.

**Corollary.** Let $\mathrm{SP}^*$ be stabbing planes restricted to coefficients of magnitude $n^{\log^{O(1)} n}$. There is a family of unsatisfiable CNF formulas $F_n$ such that every $\mathrm{SP}^*$ refutation of $F_n$ has size at least $2^{n^\epsilon}$ for a constant $\epsilon > 0$. Moreover $\mathrm{SP}^*$ is not automatable unless $\mathrm{P} = \mathrm{NP}$; that is, $\mathrm{SP}^*$ refutations cannot be found efficiently assuming $\mathrm{P} \ne \mathrm{NP}$.

## Expansion

The source converts a low-coefficient stabbing planes refutation of the polytope $P$ of $F$ into a facelike one by induction on $s$. At the root query $(ax \le b, ax \ge b + 1)$ assume the left subproof $\pi_L$ is the smaller one, $|\pi_L| \le s/2$. Replace the root by a path of queries $ax \le b_0 + i$ versus $ax \ge b_0 + i + 1$ for $i = 0, \dots, t - 1$, starting from the largest integer $b_0$ with $ax \ge b_0$ valid on $P$; each is facelike, and each slab $P \cap \{ax = b_0 + i\}$ is refuted by a copy of the facelike version of $\pi_L$. The slabs have width $1/\|a\|_2$ and $\|a\|_\infty \le c$, which bounds the number $t$ of slabs in terms of $c$, $n$ and the diameter of the polytope, and the recurrence $f(s) \le t f(s/2) + f(s_R)$ gives a quasi-polynomial bound. A CNF polytope lies in $[0,1]^n$, of diameter at most $\sqrt{n}$, and facelike stabbing planes converts to cutting planes with polynomial overhead. The source states this conversion for arbitrary polytopes as Theorem 3.7, with a bound in terms of the diameter $d(P)$; its slab estimate $t \le c\, d(P) \sqrt{n}$ breaks at the endpoint $d(P) = 0$, since $t \ge 1$ always (for $P = \{1/2\}$, refuted by the split $x \le 0$ versus $x \ge 1$, the printed bound is $0$), so only the CNF theorems are stated here. The corollary combines this with known exponential cutting planes lower bounds and with NP-hardness of automating cutting planes.

## Depends on

- [The stabbing planes proof system](../../stabbing-planes-and-semi-algebraic-branching/stabbing-planes-system.md)
- [Cutting planes equal facelike stabbing planes](cutting-planes-equal-facelike-stabbing-planes.md)
- [Automatable proof systems](../../automatability-of-proof-systems/automatable-proof-system.md)
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [The complexity class NP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)

## Proof depends on

- [Cutting planes equal facelike stabbing planes](cutting-planes-equal-facelike-stabbing-planes.md)
- [Random logarithmic-width CNFs are hard for cutting planes](../../stabbing-planes-and-semi-algebraic-branching/random-cnf-cutting-planes.md)
- [Göös–Koroth–Mertz–Pitassi: automating cutting planes is NP-hard](../../automatability-of-proof-systems/gkmp-cutting-planes.md)

## Sources

- N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson, "On the power and limitations of branch and cut", *CCC 2021*, LIPIcs 200, doi:10.4230/LIPIcs.CCC.2021.6, arXiv:2102.05019v2 (version read: Theorem 1.2, the quasi-polynomial simulation theorem, and Theorem 1.4, the $\mathrm{SP}^*$ lower bound, in Section 1; Theorem 3.7, the polytope version used in their proof, and Corollary 3.8 on non-automatability in Section 3.2; Corollary 3.8 prints "unless P $\ne$ NP", a misprint, and the sentence before it states the form used here, that such refutations cannot be found efficiently assuming P $\ne$ NP).
