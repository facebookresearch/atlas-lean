# Translating the queries of an oracle algorithm

Let $c$ be an adaptive oracle algorithm
with queries in $X$, answers in $Y$ and output in $\alpha$, and let $f : X \to P$ and
$g : X \to Z \to Y$. The translated algorithm, with queries in $P$ and answers in $Z$, runs $c$ and
replaces each query $x$ of $c$ by the query $f(x)$; on the answer $z$ it hands $g(x, z)$ to $c$ as
the answer to $x$. So, run against an oracle $O : P \to Z$, it runs $c$ against the oracle
$x \mapsto g(x, O(f(x)))$ and makes one query for each query of $c$.
