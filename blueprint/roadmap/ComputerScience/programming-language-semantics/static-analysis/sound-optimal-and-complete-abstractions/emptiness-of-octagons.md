# Emptiness of octagons

With the notation of [difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md), let $m^+$ be a coherent DBM over the $2N$ forms $v_0^+, v_0^-, \dots, v_{N-1}^+, v_{N-1}^-$, with domain $D(m^+)$ and octagon $D^+(m^+)$.

1. If the numerical set $\mathbb{I}$ is $\mathbb{Q}$ or $\mathbb{R}$, then $D^+(m^+) = \emptyset$ if and only if $D(m^+) = \emptyset$. So emptiness of an octagon reduces to emptiness of the domain of a DBM, which is decided by a search for a cycle of strictly negative weight in the potential graph $G(m^+)$, in time $O(N^3)$ with the Bellman–Ford algorithm.
2. If $\mathbb{I} = \mathbb{Z}$, then $D(m^+) = \emptyset$ implies $D^+(m^+) = \emptyset$, but not conversely. For example, the constraints $v_1 - v_0 \le 0$, $v_0 + v_1 \le 3$ and $2 v_1 \ge 3$ have integer bounds in their encoding as a DBM over the four forms, and $D(m^+)$ contains integer points, such as $(v_0^+, v_0^-, v_1^+, v_1^-) = (3, 0, 3, 0)$, none of the form $(s_0, -s_0, s_1, -s_1)$. Indeed the only real solution of the constraints is $v_0 = v_1 = 3/2$, so the octagon has no integer point.

## Depends on

- [Difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md)

## Expansion

This page becomes ready once this prerequisite is stated:

- Satisfiability of difference constraints via negative cycles: a conjunction of constraints $x - y \le c$ is unsatisfiable if and only if its constraint graph has a cycle of strictly negative weight (statement prerequisite of part 1; a page for it is added by pull request #9178 under `TheoryOfComputation/decision-procedures/satisfiability-modulo-theories`, to be linked once that pull request is on main).

## Sources

- A. Miné, "The octagon abstract domain", arXiv:cs/0703084v2, 2007, <https://arxiv.org/abs/cs/0703084>: Section V.A, Theorem 2 (parts 2 and 3) and the use of the Bellman–Ford algorithm, with the counterexample of Figure 6.
