# Interpolants from resolution refutations

Clauses are non-tautological sets of literals. The resolvent of $c_1 = v \vee a$ and $c_2 = \neg v \vee b$ is $a \vee b$, provided it is
non-tautological, and $v$ is the *pivot*. A *proof of unsatisfiability* $\Pi$ of a clause set $C$ is a directed acyclic graph whose vertices are
clauses, such that every vertex either is a clause of $C$ and a root, or has exactly two predecessors of which it is the resolvent,
and the empty clause is the unique leaf.

Let $A$ and $B$ be clause sets and $\Pi$ a proof of unsatisfiability of $A \cup B$. A variable is *global* if it occurs in both $A$ and $B$, and
*local to $A$* if it occurs only in $A$; for a clause $c$, $g(c)$ is the disjunction of its global literals. Label each vertex $c$ of $\Pi$ by a
formula $p(c)$: a root in $A$ gets $g(c)$, any other root gets $\mathrm{true}$, and a resolvent of $c_1, c_2$ with pivot $v$ gets $p(c_1) \vee p(c_2)$ if $v$
is local to $A$ and $p(c_1) \wedge p(c_2)$ otherwise. Then $\mathrm{Itp}(\Pi, A, B) = p(\text{empty clause})$ is an interpolant of $(A, B)$:

- $A$ implies $\mathrm{Itp}(\Pi, A, B)$;
- $\mathrm{Itp}(\Pi, A, B) \wedge B$ is unsatisfiable;
- $\mathrm{Itp}(\Pi, A, B)$ contains only global variables.

It can be computed in time $O(N + L)$, where $N$ is the number of vertices of $\Pi$ and $L$ the total number of literal occurrences in its
clauses, and its circuit, which shares the labels of common subproofs, has size $O(N + L)$.

## Sources

- K. L. McMillan, "Interpolation and SAT-based model checking", *CAV 2003*, LNCS 2725, Springer, 2003: Section 2 (resolvents, Definition 1, Definition 2, Theorem 2 and the complexity remark after it).
