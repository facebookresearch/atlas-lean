# Reachability from a seed by generators

Let $F$ be a finite set of functions
$\mathbb{N} \to \mathbb{N}$ and let $s \in \mathbb{N}$. Reachability from $s$ is the least
predicate on $\mathbb{N}$ that holds at $s$ and holds at $f(w)$ whenever it holds at $w$ and
$f \in F$. Thus $y$ is reachable exactly when $y = f_k(\cdots f_1(s) \cdots)$ for some $k \ge 0$
and $f_1, \ldots, f_k \in F$; the case $k = 0$ is $s$ itself.
