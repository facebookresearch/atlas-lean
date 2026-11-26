# Context-free-language reachability

Let $L$ be a context-free language over an alphabet $\Sigma$ and let $G$ be a directed graph whose edges are labeled with letters of $\Sigma$. The word of a path in $G$ is the concatenation of the labels of its edges, and the path is an *$L$-path* if its word lies in $L$. The *CFL-reachability* problems for $L$ are:

- *all pairs*: find all pairs of nodes $n_1, n_2$ joined by an $L$-path from $n_1$ to $n_2$;
- *single source*: given $n_1$, find all $n_2$ reachable from $n_1$ by an $L$-path;
- *single target*: given $n_2$, find all $n_1$ from which $n_2$ is reachable by an $L$-path;
- *single source, single target*: decide whether an $L$-path leads from a given $n_1$ to a given $n_2$.

Ordinary reachability is the case $L = e^*$ with every edge labeled $e$. Recognition of a word $\omega$ in $L$ is the single-source, single-target problem on a path of $|\omega|$ edges labeled by the letters of $\omega$. Interprocedural *realizable* paths, whose calls and returns $(_i$ and $)_i$ are partially balanced, are the $L$-paths for a language of partially balanced parentheses.

## Sources

- T. Reps, "Program analysis via graph reachability", technical report, University of Wisconsin, <https://research.cs.wisc.edu/wpis/papers/tr1386.pdf> (also *Information and Software Technology* 40(11–12):701–726, 1998), Section 2: Definition 2.1, the relationship with ordinary reachability and with context-free recognition, and the languages $L(\mathit{matched})$ and $L(\mathit{realizable})$ over a supergraph.
