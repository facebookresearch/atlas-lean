# Left-hand side of the clause constraint of the MAX SAT relaxation

Let $C_j$ be a clause, a list of literals, each a variable $x_i$ or its negation $\bar x_i$, and let
$y_i \in \mathbb{R}$ for every variable index $i$. The clause bound of $C_j$ at $y$ is the sum, over
the literals of $C_j$ counted with multiplicity, of $y_i$ for a literal $x_i$ and of $1 - y_i$ for a
literal $\bar x_i$. It is the left-hand side of the constraint $z_j \le \ldots$ of the integer
program (IP) and its relaxation (LP). For a clause whose literals use distinct variables, with
positive variables $P_j$ and negated variables $N_j$, it is
$\sum_{i \in P_j} y_i + \sum_{i \in N_j} (1 - y_i)$; a repeated literal counts once for each
occurrence: for $C_j = (x_1, x_1)$ it is $2 y_1$.

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), §3.
