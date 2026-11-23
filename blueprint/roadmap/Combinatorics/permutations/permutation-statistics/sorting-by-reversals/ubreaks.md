# Unsigned breakpoint count of a list framed by 0 and n + 1

For a natural number $n$ and a list of integers $\pi = (\pi_0, \dots, \pi_{m-1})$, the unsigned
breakpoint count $b_n(\pi)$ is the [gap count](gap-count.md) of the framed list
$\ell = (0, \pi_0, \dots, \pi_{m-1}, n + 1)$: the number of $k$ with $0 \le k \le m$ and
$|\ell_{k+1} - \ell_k| \ne 1$, that is, of adjacent pairs of the framed list that are not
consecutive integers in either order. It is defined for every list and every $n$, and $n$ need
not be the length of $\pi$: for the empty list it is $0$ if $n = 0$ and $1$ otherwise. For a
[permutation](uvalid.md) of $1, \dots, n$ it is the number of breakpoints of Shamir and Peer
(Lecture 11, §11.2).
