# The PRG distinguisher built from a PRF adversary against the GGM construction

Let $S$
and $R$ be finite nonempty sets, let $G : S \to S \times S$, write $G(s) = (G_0(s), G_1(s))$, let
$\ell \ge 1$ and $Q \ge 1$, and let $A$ be a PRF adversary against the GGM construction: for coins
$r \in R$, $A(r)$ is an adaptive oracle algorithm with queries in $\{0,1\}^\ell$, answers in $S$
and a bit as output. Write a query
as $x = x_0 \cdots x_{\ell-1}$. The distinguisher $B$ receives a pair $y \in S \times S$. Its
coins, drawn uniformly, are a level $i \in \{0, \dots, \ell - 1\}$, a hybrid index
$j \in \{0, \dots, Q - 1\}$, pairs $u_0, \dots, u_{Q-1} \in S \times S$, seeds
$v_0, \dots, v_{Q-1} \in S$ and coins $r$ for $A$. It runs $A(r)$ once and outputs its output,
answering the queries of $A$ itself from a table that records, for nodes $p$ at level $i$ of the
evaluation tree, a pair of labels for the two children of $p$. The $m$-th query $x$ (counting
from $0$) concerns the node $p = x_0 \cdots x_{i-1}$. If the table has a pair for $p$, it is
reused; otherwise the pair is $u_m$ if $m < j$, the challenge $y$ if $m = j$ and $G(v_m)$ if
$m > j$, and it is recorded for $p$. From the pair $(a_0, a_1)$ for $p$, the answer to $x$ is
$G_{x_{\ell-1}}(\cdots G_{x_{i+1}}(a_{x_i}) \cdots)$. A query for a node with no pair in the table,
asked after the first $Q$ queries, makes $B$ stop and output $0$; an adversary that makes at most
$Q$ queries never asks one.

So $B$ runs $A$ once, keeps a table of at most $Q$ entries and evaluates $G$ at most $\ell$ times
per query of $A$.
