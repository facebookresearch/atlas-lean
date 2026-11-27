# Six-part correctness of Boolean quadtree operations

For Boolean region quadtrees, with lookups of a cell $(i, j)$ at a scale $n$:

1. for all $n, i, j$ and $s, t$ with the heights of $s$ and $t$ at most $n$, the lookup in
   $s \cup t$ is the disjunction of the lookups in $s$ and in $t$;
2. for all $n, i, j$ and $s, t$ with the heights of $s$ and $t$ at most $n$, the lookup in
   $s \setminus t$ is true exactly when the lookup in $s$ is true and the lookup in $t$ is false;
3. for all $s, t$, the height of $s \cup t$ is at most the maximum of the heights of $s$ and $t$;
4. for all $s, t$, the height of $s \setminus t$ is at most the maximum of the heights of $s$ and
   $t$;
5. for all compressed $s, t$, the union $s \cup t$ is compressed;
6. for all compressed $s, t$, the difference $s \setminus t$ is compressed.

## Sources

- T. Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof Assistant Approach*, ACM
  Books, 2025 (author's version of 27 July 2026: https://fdsa-book.net/), Section 13.1, Exercise 13.1.
