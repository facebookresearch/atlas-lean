# Subsumption between control-flow coverage criteria

Fix a program with control-flow graph $G$, a directed graph whose nodes are the basic blocks and whose edges are the
possible control transfers. A test set determines the set $P$ of execution paths of $G$ that its test cases follow. $P$
satisfies *statement coverage* if every node of $G$ lies on some path in $P$, and *branch coverage* if every edge of $G$ lies
on some path in $P$. For a program whose conditions are Boolean combinations of atomic predicates, a test set satisfies
*condition coverage* if every atomic predicate of every condition evaluates to true in some test case and to false in
some test case, and *multiple condition coverage* if for every condition with atomic predicates $p_1, \dots, p_n$ and every
assignment $(b_1, \dots, b_n)$ of truth values, some test case evaluates each $p_i$ to $b_i$. A criterion $C_1$ *subsumes* $C_2$ if
for every program and every test set, adequacy for $C_1$ implies adequacy for $C_2$.

- If every node of $G$ is an endpoint of some edge, every path set satisfying branch coverage satisfies statement
  coverage. Hence branch coverage subsumes statement coverage on flow graphs in which every node is an endpoint of an edge, in particular on connected flow graphs with at least two nodes.
- Statement coverage does not subsume branch coverage: for $\mathbf{if}\ b\ \mathbf{then}\ s$ with no else part, the single path
  through $s$ covers every node but not the edge from the test of $b$ directly to the join node.
- Multiple condition coverage subsumes condition coverage, since among all truth assignments to $p_1, \dots, p_n$ each $p_i$
  takes both values.

These are the unrestricted criteria. With infeasible nodes or edges no test set may satisfy them, and their feasible
versions require covering only feasible elements.

## Sources

- H. Zhu, P. A. V. Hall and J. H. R. May, "Software unit test coverage and adequacy", *ACM Computing Surveys* 29(4):366–427, 1997: Definitions 2.1, 2.2 and 2.5, the condition-coverage definition in Section 2.1.1, the discussion of infeasible elements, and Definition 5.1 (subsume relation).
