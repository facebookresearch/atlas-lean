# Switching lists after the first request

Let $M$ be a list of length $\ell$ and $R$ a list,
and write $\mathrm{inv}(M, R)$ for the number of inversions between $M$ and $R$. For every request
sequence $\sigma$ of items of $M$, the offline cost (without free exchanges) of serving $\sigma$
with the lists $M, R, R, R, \dots$ is at most $\ell + \mathrm{inv}(M, R)$ plus the static cost of
serving $\sigma$ with $R$.
