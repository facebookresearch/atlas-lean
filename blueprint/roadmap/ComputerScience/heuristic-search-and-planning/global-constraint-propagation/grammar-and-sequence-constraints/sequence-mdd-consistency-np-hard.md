# MDD consistency for SEQUENCE is NP-hard

Although domain consistency for SEQUENCE takes polynomial time, deciding whether a SEQUENCE constraint has a solution on a given multivalued decision diagram, and hence establishing MDD consistency for it, is NP-hard, even when the diagram follows the variable order of the constraint and has width at most six.

Use [ordered MDDs and MDD consistency](mdd-consistency.md) and the [SEQUENCE constraint](sequence-constraint.md) in the form $\mathrm{Sequence}(Y,q,l,u,S)$: the conjunction of AMONG with bounds $l,u$ and value set $S$ over every window of $q$ consecutive variables of the ordered sequence $Y$.

Instances are encoded as bitstrings in a format whose well-formedness is decidable in polynomial time, and malformed strings are rejected. A decision problem is NP-hard when every problem in NP has a polynomial-time many-one reduction to it.

**Theorem.** The following problem is NP-hard: given an ordered MDD $M$ on 0/1 variables $Y$ and a constraint $\mathrm{Sequence}(Y,q,l,u,\{1\})$ on the same variable order, decide whether $M$ contains a path feasible for the constraint. It remains NP-hard when $M$ has width at most six and $q=2N$, $l=u=N$ for a number $N\ge1$ given with the instance. Consequently, unless P $=$ NP, MDD consistency for SEQUENCE cannot be established in polynomial time, since establishing it removes every arc exactly when no feasible path exists.

## Depends on

- [MDD consistency](mdd-consistency.md): ordered MDDs, feasible paths and MDD consistency.
- [AMONG and SEQUENCE constraints](sequence-constraint.md): the constraint.
- [Polynomial-time many-one reduction](../../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md): the reduction.
- [The complexity class NP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md): NP-hardness.
- [The complexity class P](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md): the conclusion unless P $=$ NP.

## Proof depends on

- [3SAT is NP-complete](../../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/sat3-dec-np-complete.md): the reduction is from 3SAT.

## Expansion

The reduction is from 3SAT on bitstrings. Inputs that do not decode to a CNF formula with at most three literals per clause, and formulas with an empty clause, go to the fixed no-instance built below from $x_1\wedge\neg x_1$; a formula without clauses goes to the fixed yes-instance built from $x_1$; both lie in the restricted class. Otherwise rename the variables to $x_1,\dots,x_N$; since some clause is nonempty, $N\ge1$. For such a formula with $N\ge1$ variables and $m\ge1$ nonempty clauses $c_1,\dots,c_m$, take 0/1 variables $y_{i,j},\bar y_{i,j}$ (literal $x_j$, resp. $\neg x_j$, chosen true in clause $c_i$), ordered clause by clause and within a clause by $j$, $y_{i,j}$ before $\bar y_{i,j}$, and build an MDD with $2mN+1$ layers. Within the block of clause $c_i$, a "diamond" lets each pair $(y_{i,j},\bar y_{i,j})$ be $(1,0)$ or $(0,1)$, the nodes are tagged sat/unsat according to whether a literal of $c_i$ has been made true, and only sat nodes survive, merged into one node, to the next block and finally to the terminal. Each layer has at most six nodes. Imposing $\mathrm{Sequence}(Y,2N,N,N,\{1\})$ forces exactly $N$ ones in every window of $2N$ consecutive variables; a window starting at a negative literal $\bar y_{i,j}$ ends at $y_{i+1,j}$, which forces $x_j$ to take the same value in clause blocks $i$ and $i+1$. So the MDD has a feasible path iff the formula is satisfiable, and the construction is polynomial.

The source states the theorem as "establishing MDD consistency for Sequence on an arbitrary MDD is NP-hard even if the MDD follows the variable ordering of the Sequence constraint", and proves it by exactly this reduction to the existence of a feasible path. Establishing MDD consistency is nonetheless fixed-parameter tractable in the window length $q$, by intersecting with an exact MDD of SEQUENCE.

## Sources

- D. Bergman, A. A. Cire and W.-J. van Hoeve, "MDD propagation for sequence constraints", *Journal of Artificial Intelligence Research* 50 (2014), 697–722, doi:10.1613/jair.4199. Theorem 1 and its proof with Example 1 and Figure 1, §3, pp. 701–704.
