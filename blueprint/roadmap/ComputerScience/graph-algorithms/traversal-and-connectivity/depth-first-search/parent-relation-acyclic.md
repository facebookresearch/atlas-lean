# The DFS parent relation is acyclic

Let $G$ be a finite directed graph and $R$ a list of
root vertices, and run depth-first search on $G$ from $R$. Say that $p$ is a recorded parent of $c$
when the pair $(c, p)$ occurs in the list of (child, parent) pairs recorded by the search. Then
there are no $k \ge 1$ and vertices $v_0, v_1, \dots, v_k$ with $v_k = v_0$ such that each
$v_{i+1}$ is a recorded parent of $v_i$.
