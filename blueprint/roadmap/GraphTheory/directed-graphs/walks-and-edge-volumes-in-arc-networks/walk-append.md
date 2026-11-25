# Splitting a concatenated walk

Let $V$ and $E$ be sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$. A list of arcs is a walk from $o$ to $d$ if it is empty only when $o = d$, its first arc leaves $o$, the head of each arc is the tail of the next, and its last arc enters $d$. If the concatenation $l_1 \mathbin{+\!\!+} l_2$ of two arc lists is a walk from $o$ to $d$, then there is a vertex $m$ such that $l_1$ is a walk from $o$ to $m$ and $l_2$ is a walk from $m$ to $d$.
