# Orbit-finite integer linear programming is undecidable

No algorithm decides whether an orbit-finite system of linear inequalities has a finitary integer solution, although the same question over the reals is decidable. The reduction from counter machines produces systems of atom dimension $3$.

**Theorem (Ghosh, Hofman and Lasota).** The problem $\mathrm{FinIneqSolv}(\mathbb{Z})$ is undecidable: there is no algorithm that, given an orbit-finite system of linear inequalities $(\vec{A}, \vec{t})$ over equality atoms, with $\vec{A} : B \times C \to \mathbb{Z}$ and $\vec{t} : B \to \mathbb{Z}$ finitely supported and $B, C$ orbit-finite, decides whether there is a finitary integer vector $\vec{x}$ over $C$ with $\langle \vec{A}(b, \cdot), \vec{x} \rangle \ge \vec{t}(b)$ for all $b \in B$.

By the inter-reducibility of the variants for a fixed ring (Theorem 17 of the arXiv version), undecidability transfers to integer solvability with arbitrary finitely supported solutions and to nonnegative integer solvability of orbit-finite systems of equations. In contrast, $\mathrm{FinIneqSolv}(\mathbb{R})$ is decidable in exponential time, and in polynomial time for fixed atom dimension (Theorem 18). The authors note that their reduction yields systems of atom dimension $3$ and leave open whether dimension $2$ suffices.

## Depends on

- [Orbit-finite systems of linear inequalities](orbit-finite-systems-of-linear-inequalities.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from reachability for $d$-counter machines with zero tests: each instruction assigns to every counter either an integer increment or a zero test, and the question is whether a run leads from a source configuration $c_0 \in \mathbb{N}^d$ to a target $c_f$. This is undecidable because such machines simulate Minsky machines. Nonnegativity is enforced by inequalities $x \ge 0$. Unknowns $e_{\alpha\beta} \le 1$ indexed by pairs of distinct atoms describe a directed graph on atoms, and degree constraints force a finitary solution to contain a path from a fixed atom $\iota$ to a fixed atom $\zeta$; further unknowns and inequalities attach instructions and counter values to the steps of this path and check that consecutive steps respect the instructions, including the zero tests, so that $M$ has a run from $c_0$ to $c_f$ if and only if the system has a finitary nonnegative integer solution. A good expansion links a page for the undecidability of reachability between two given configurations of counter machines with zero tests, the problem the reduction starts from.

## Sources

- Arka Ghosh, Piotr Hofman and Sławomir Lasota, "Orbit-finite Linear Programming", Journal of the ACM 72(1), 39 pages, 2025, <https://doi.org/10.1145/3703909>; Theorem 19 (main statement), Theorems 17 and 18, the open questions in Section 10 and the proof in Section 9 of arXiv:2302.00802v4, <https://arxiv.org/abs/2302.00802v4>.
- Arka Ghosh, Piotr Hofman and Sławomir Lasota, "Orbit-finite linear programming", 38th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2023), pp. 1–14, 2023, <https://doi.org/10.1109/LICS56636.2023.10175799>; conference version, not read (the statements rest on the version read of the first source above).
