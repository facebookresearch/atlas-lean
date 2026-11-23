# Right-end gap is unchanged by doubling for absolute value at most n

For a natural number $n$ and an integer $x$ with $|x| \le n$, the [gap indicator](is-gap.md) of the
second entry $\delta_2(x)$ of the [doubled pair](dbl-one.md) of $x$ and $2n + 1$ equals the
[directed gap indicator](is-dir-gap.md) of $(x, n + 1)$: $|2n + 1 - \delta_2(x)| = 1$ if and only if
$x = n$. This compares the last adjacent pair of a signed list framed on the right by $n + 1$ with
that of its doubled list, framed by $2n + 1$ (Shamir and Peer, Lecture 11, signed setting); $x = 0$
is allowed. For $x = n + 1$ the equality fails: $\delta_2(n + 1) = 2n + 2$ is one apart from
$2n + 1$, but $(n + 1) - x = 0$.
