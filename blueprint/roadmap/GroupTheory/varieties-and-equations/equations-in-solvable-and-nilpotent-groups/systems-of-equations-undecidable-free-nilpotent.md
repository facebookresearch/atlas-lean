# Systems of equations are undecidable in every non-abelian free nilpotent group

No algorithm decides whether a finite system of equations with constants has a solution in a free nilpotent group of step $p \ge 2$ and rank $q \ge 2$; in particular in the Heisenberg group. A single equation in the Heisenberg group is decidable.

Let $N(p, q)$ be the free nilpotent group of step (class) $p \ge 2$ and rank $q \ge 2$, and let $H(\mathbb{Z})$ be the integer Heisenberg group, which is $N(2, 2)$. Let $\mathcal{EP}$ be the problem of deciding whether a finite system of equations with constants has a solution. Then (source):

1. $\mathcal{EP}$ is undecidable in $N(2, q)$ for every $q \ge 2$, in particular in $H(\mathbb{Z})$ (Theorem 4);
2. $\mathcal{EP}$ is undecidable in every free nilpotent group of step at least $3$ (Proposition 6).

By contrast, there is an algorithm deciding any single equation in $H(\mathbb{Z})$, and more generally in every finitely generated two-step nilpotent group whose commutator subgroup has rank one, that is, is virtually $\mathbb{Z}$ (Theorem 3). Earlier results recalled in the source: Roman'kov exhibited a four-step nilpotent group with undecidable $\mathcal{EP}$, and $\mathcal{EP}$ is undecidable in $N(2, q)$ for $q$ large (Durnev) and in $N(3, 2)$ (Truss).

## Depends on

- [Group](../../group-basics/group.md)
- [Free group of a variety on a finite set](../automorphisms-of-categories-of-relatively-free-g/relatively-free-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Solution set of a system of equations](../equationally-noetherian-groups/solutions-2.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

A system of quadratic Diophantine equations $\alpha_i + \sum_j \beta_{ij} x_j + \sum_{j,k} \gamma_{ijk} x_j x_k = 0$ in $n$ integer unknowns $x_1, \dots, x_n$ is encoded in $N(2, q)$ by a system with twice as many variables and $3n$ extra equations, the three equations $[a, y_j] = 1$, $[b, y'_j] = 1$ and $[b, y_j] = [y'_j, a]$ for each unknown (the source writes $3q$ and $1 \le j \le q$, a slip for the number of unknowns), that force each variable into a cyclic subgroup modulo the commutator subgroup, so that commutators multiply exponents. In step $p \ge 3$ the source uses iterated commutators $[R, b, y_j]$ and $[R, y_j, y_k]$ with $R = [a, b, \dots, b]$. Solvability of systems of quadratic Diophantine equations is undecidable by Matiyasevich's theorem, since every Diophantine equation reduces to such a system by introducing auxiliary variables.

## Sources

- M. Duchin, H. Liang and M. Shapiro, "Equations in nilpotent groups", Proceedings of the American Mathematical Society 143 (2015), no. 11, 4723–4731, https://doi.org/10.1090/proc/12630; read in arXiv:1401.2471v1, whose numbering is used here (Theorems 3 and 4 and Proposition 6 of arXiv:1401.2471v1).
