# Upper bound on the prefix transposition diameter

**Setting.** Model a genome with $n$ distinct markers as a permutation $\pi\in S_n$ of $\{0,1,\dots,n-1\}$. A *transposition* moves a contiguous sublist to another position; a *prefix transposition* is a transposition whose moved sublist starts at the first position, $(\pi_1,\dots,\pi_i)$ being reinserted after position $j$ with $i<j\le n$. The prefix transposition distance $d(\pi)$ is the least number of prefix transpositions sorting $\pi$ to the identity $I_n$, and the prefix transposition diameter is $D(n)=\max_{\pi\in S_n}d(\pi)$.

**Theorem.** For every $n\ge1$,

$$
D(n)\le n-1 .
$$

The bound is attained for $2\le n\le 7$; for example, from $(2,1,0)$ the only single moves give $(1,2,0)$, $(1,0,2)$ and $(0,2,1)$, so $d(2,1,0)=2$. In particular expressions such as $n-\log_2 n$ are not upper bounds on $D(n)$ for every $n$: $D(3)=2>3-\log_2 3$, and $D(4)=3>4-\log_2 4$.

## Expansion

Let $(m,m+1,\dots,n-1)$ be the longest suffix of $\pi$ that is a run of consecutive values ending in $n-1$, with $m=n$ when $\pi$ does not end in $n-1$. If $m=0$, then $\pi=I_n$. Otherwise $m-1$ sits at some position $i$ before the suffix, and $i<n-(n-m)$, since otherwise $m-1$ would already precede $m$ and extend the suffix. Moving the prefix $(\pi_1,\dots,\pi_i)$, which ends in $m-1$, to just before the suffix makes $m-1,m,\dots,n-1$ a sorted suffix, so each move lengthens the sorted suffix by at least one. A sorted suffix of length $n-1$ forces $\pi_1=0$ and $\pi=I_n$; the first move gives a suffix of length at least $1$, so at most $n-1$ moves are needed.

## Sources

- Z. Dias and J. Meidanis, *Sorting by prefix transpositions*, in: String Processing and Information Retrieval (SPIRE 2002), Lecture Notes in Computer Science 2476, Springer (2002) 65–76. <https://doi.org/10.1007/3-540-45735-6_7> The upper bound $n-1$ on the prefix transposition distance.
