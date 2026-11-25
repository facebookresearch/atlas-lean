# Ancestral paths from an individual

In a [pedigree](pedigree.md), the set of ancestral paths from $i$ is defined by recursion on $i$: it is $\{(i)\}$ if $i$ is a founder, and otherwise it consists of $(i)$ together with the sequences $(i, v_1, \dots, v_k)$ such that $(v_1, \dots, v_k)$ is an ancestral path from a parent $v_1 \in \{f(i), m(i)\}$. These are the sequences $i = v_0, v_1, \dots, v_k$, $k \ge 0$, in which each $v_{t+1}$ is a parent of $v_t$.
