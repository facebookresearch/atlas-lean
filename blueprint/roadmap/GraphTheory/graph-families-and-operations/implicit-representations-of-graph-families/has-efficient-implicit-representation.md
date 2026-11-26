# Efficient implicit representation

A family of labelled graphs $(F_n)$ has an efficient implicit representation when there are a natural number $c$ and, for each $n$, a decoder taking two binary strings of length $c(\lfloor \log_2 n \rfloor + 1)$ to a bit, such that every member $G \in F_n$ has an assignment of such strings (codes) to its vertices with $u \sim v$ in $G$ exactly when the decoder returns $1$ on the codes of $u$ and $v$, for all distinct $u, v$. The decoder may depend on the family and on $n$ but not on $G$; no computability of the decoder is required.

Here $\lfloor \log_2 n \rfloor$ is the integer logarithm, taken as $0$ for $n = 0$.
