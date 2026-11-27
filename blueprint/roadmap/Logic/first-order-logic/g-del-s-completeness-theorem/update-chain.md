# Replacing arguments one at a time

Let $r$ be a relation on a type $\beta$, let $n$ be a
natural number and let $P$ be a property of $n$-tuples $x = (x_i)_{i < n}$ in $\beta$. Suppose
that for every tuple $x$, every position $i$ and all $a, b \in \beta$ with $r(a, b)$, if $P$
holds of $x$ with its $i$-th entry replaced by $a$, then $P$ holds of $x$ with its $i$-th entry
replaced by $b$. Then for all tuples $x, y$ with $r(x_i, y_i)$ for every $i$, $P(x)$ implies
$P(y)$.
