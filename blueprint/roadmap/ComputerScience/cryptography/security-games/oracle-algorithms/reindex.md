# Translating the queries of an oracle algorithm

Let $c$ be an adaptive oracle algorithm
with queries in $X$, answers in $Y$ and output in $\alpha$, and let $f : X \to P$ and
$g : X \to Z \to Y$. The translated algorithm, with queries in $P$ and answers in $Z$, runs $c$ and
replaces each query $x$ of $c$ by the query $f(x)$; on the answer $z$ it hands $g(x, z)$ to $c$ as
the answer to $x$. So it makes one query for each query of $c$.
