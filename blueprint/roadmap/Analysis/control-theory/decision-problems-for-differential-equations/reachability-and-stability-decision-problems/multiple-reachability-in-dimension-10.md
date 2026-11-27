# Multiple reachability for linear dynamical systems is undecidable in dimension 10

No algorithm decides, given semialgebraic source and target sets in ℝ¹⁰ and a rational 10 × 10 matrix, whether some source point has an orbit meeting the target in at least 9 distinct points; for multiplicity 1 it is the Reachability Problem, which includes Skolem's Problem (point-to-hyperplane reachability), whose decidability is open.

**Setting.** For $M \in \mathbb Q^{d \times d}$ and $p \in \mathbb R^d$ (a row vector) the orbit is $O_M(p) = \{p M^n : n \in \mathbb N\}$. A semialgebraic set is given by a Boolean combination of polynomial inequalities with rational coefficients. The *Multiple Reachability Problem* asks, given semialgebraic $S, T \subseteq \mathbb R^d$, a matrix $M \in \mathbb Q^{d \times d}$ and a positive integer $m$, whether there is $p \in S$ with $|O_M(p) \cap T| \ge m$.

**Theorem (Karimov, Kelmendi, Ouaknine and Worrell).** The Multiple Reachability Problem is undecidable, already in dimension $d = 10$ with fixed multiplicity $m = 9$, with a semialgebraic source set and a hyperplane as target. With an algebraic source set and a hyperplane target it is undecidable in dimension $19$ with $m = 9$.

In the reduction the matrix is not diagonalizable. The same paper proves that in dimension $2$ multiple reachability is decidable when $M$ is a rotation and, for any $M$, when the target is a half-plane.

## Depends on

- [Semialgebraic set](../../../../Logic/model-theory/wilkie-s-conjecture/is-semialgebraic.md)
- [Skolem, positivity and bounded reachability problems for LRS](../../../../NumberTheory/linear-recurrences/skolem-positivity-and-bounded-reachability-problems-for-lrs.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof uses "Hilbert's tenth problem over the natural numbers is undecidable with nine unknowns", which has no page on main yet; link it once its page lands.

The proof reduces from a variant of Hilbert's tenth problem: given $P \in \mathbb Z[x_1, \ldots, x_k]$, are there distinct positive integers $n_1, \ldots, n_k$ with $P(n_1, \ldots, n_k) = 0$? This variant is undecidable because Hilbert's tenth problem is (by the Davis–Putnam–Robinson–Matiyasevich theorem), and already for fixed $k = 9$ by Jones's result that Hilbert's tenth problem is undecidable with $9$ unknowns (linked above; it is stated over $\mathbb N$, and the shift $x \mapsto x + 1$ passes to positive integers). Every univariate polynomial of degree $d$ satisfies the same linear recurrence, which turns into a matrix; from $P$ one builds an algebraic source set whose points' orbits hit a fixed hyperplane at times forming a root of $P$ in distinct positive integers. A decision procedure in dimension $2n + 1$ (algebraic source) or $n + 1$ (semialgebraic source, after projecting away auxiliary coordinates) would therefore solve Diophantine equations in $n$ unknowns.

## Sources

- Toghrul Karimov, Edon Kelmendi, Joël Ouaknine and James Worrell, "Multiple reachability in linear dynamical systems", in *2025 40th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS)*, IEEE, 2025, pp. 651–663, <https://doi.org/10.1109/LICS65433.2025.00055>; read as arXiv:2403.06515v2, <https://arxiv.org/abs/2403.06515v2>: the problem in Section I, Theorem I.1 and Theorem I.2, and Proposition III.2, Proposition III.3 and Theorem III.6 of Section III, of that version.
