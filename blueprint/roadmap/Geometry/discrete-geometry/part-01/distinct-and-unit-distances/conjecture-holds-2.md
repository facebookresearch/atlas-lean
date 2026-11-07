# Bhowmick's theorem on rich distances

For a finite set $A$ of points in the Euclidean plane,
call a distance $k$-rich for $A$ if at least $k$ unordered pairs of distinct points of $A$ lie at
that distance, and let $f(n)$ be the largest number of $(n+1)$-rich distances of a set of $n$
points. Then there is a constant $C$ with $n \le C f(n)$ for all sufficiently large $n$; for every
$n$ there is a set of $n$ points with at least $\lfloor n/4 \rfloor$ distances that are
$(n+1)$-rich; and for every $m \ge 1$ there is an $N$ such that for every $n \ge N$ there is a set
of $n$ points with at least $\lfloor n/(2(m+1)) \rfloor$ distances that are $(n+m)$-rich.

## Sources

- K. Bhowmick, A problem of Erdős about rich distances, arXiv:2407.01174 (2024), https://arxiv.org/abs/2407.01174; External Lean proof of Erdős Problem 756, https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos756.lean.
