# Signed breakpoint count of a list framed by 0 and n + 1

For a natural number $n$ and a list of integers $\pi = (\pi_0, \dots, \pi_{m-1})$, the signed
breakpoint count $b^{\pm}_n(\pi)$ is the [directed gap count](dir-gap-count.md) of the framed
list $\ell = (0, \pi_0, \dots, \pi_{m-1}, n + 1)$: the number of $k$ with $0 \le k \le m$ and
$\ell_{k+1} - \ell_k \ne 1$. An adjacent pair $(-3, -2)$ is not a breakpoint, since
$-2 - (-3) = 1$, while $(2, 1)$ is. The count is defined for every list and every $n$, and $n$
need not be the length of $\pi$; for a [signed permutation](svalid.md) of $1, \dots, n$ it is
the signed breakpoint count of Shamir and Peer (Lecture 11, signed setting).
