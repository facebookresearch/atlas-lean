# AGM tightness and the cost of projection-free join plans

This node collects the tightness of the AGM output-size bound and the separation between join plans
and worst-case optimal join algorithms.

## Expansion

A sound expansion has separate pages for:

1. **AGM tightness.** For every full join query $Q$, every optimal fractional edge cover $(x_R)$ of $Q$ and
   every $N_0$, there is a database $D$ with $\lvert D \rvert \ge N_0$ and
   $\lvert Q(D) \rvert \ge \prod_R \lvert R(D) \rvert^{x_R}$, in which the relations with $x_R > 0$ have equal
   size (by LP duality and a product construction); consequently there are arbitrarily large databases
   with $\lvert Q(D) \rvert \ge (\lvert D \rvert / \lvert Q \rvert)^{\rho^*(Q)}$. The upper bound is the linked
   AGM page and is not restated.
2. **Triangle separation.** For the triangle query and every even $N$, there are relations of $N$ tuples
   each on which every pairwise join has $N^2/4 + N/2$ tuples while the output is empty, so every
   pairwise join plan has an intermediate result of size $\Omega(N^2)$, whereas every output has at most
   $N^{3/2}$ tuples.
3. **General separation family.** For every $M$ and $N$ there are a join query $Q$ with
   $\lvert Q \rvert \ge M$ and a database $D$ with $\lvert D \rvert \ge N$ such that $Q$ has a fractional edge
   cover of weight $2$ (so $\lvert Q(D) \rvert \le \lvert D \rvert^2$) and every join plan that is correct on all
   databases has a subplan $\psi$ with $\lvert \psi(D) \rvert \ge \lvert D \rvert^{c \log_2 \lvert Q \rvert}$ for an
   explicit constant $c > 0$, while the prefix join-project plan evaluates $Q(D)$ with all intermediate
   results polynomial in $\lvert Q \rvert \cdot \lvert D \rvert$. The page states the family, its output count and
   the constants exactly. The output count must include the answers that take values other than $1$ on
   two complementary attributes $a_s$, $a_{[2m] \setminus s}$, which share no relation; the database must
   be taken large enough relative to $\lvert Q \rvert$ for the exponent comparison to hold.
4. **Cost measure.** A materialization statistic for a plan, the sum over plan nodes $v$ of
   $1 + \mathrm{arity}(v)\,(1 + \lvert R_v(D) \rvert)$, its bound on the family of item 3 for the
   prefix join-project plan, and, as a separate obligation, its relation to running time in an explicit
   RAM model; a bound on the statistic is not a running-time bound until that bridge is proved.
5. **Join-project plans on all instances.** For every join query $Q$ there is a join-project plan,
   computable from $Q$ in polynomial time, that evaluates $Q(D)$ on every database $D$ in time
   $O(\lvert Q \rvert^2 \cdot \lvert D \rvert^{\rho^*(Q)+1})$ in the uniform-cost RAM model of the cited source, as its
   own page.

## Depends on

- [AGM output-size bound for join queries](agm-output-size-bound-for-join-queries.md)
- [Natural join queries, their hypergraphs and fractional edge covers](natural-join-queries-their-hypergraphs-and-fractional-edge-c.md)

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- Size Bounds and Query Plans for Relational Joins (Atserias, Grohe, Marx), SIAM J. Comput. 42(4) 2013 — SIAM Journal on Computing, Introduction p.1739 (lower bound $(\lvert D \rvert/\lvert Q \rvert)^{\rho^*}$ and the join-plan versus join-project-plan separation), Lemma 4, Fact 5 and Theorem 6, Theorem 7 and Lemma 8. <http://www.cs.bme.hu/~dmarx/papers/atserias-sicomp2013-joins.pdf>
- Worst-case Optimal Join Algorithms (Ngo, Porat, Re, Rudra), arXiv:1203.1952 — arXiv (PODS 2012 best paper), Example 2.2 (triangle instances on which every pairwise join is quadratic). <https://arxiv.org/pdf/1203.1952>
