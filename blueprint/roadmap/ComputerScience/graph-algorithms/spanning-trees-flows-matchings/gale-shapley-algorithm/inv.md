# Invariant of deferred acceptance

Let each proposer $m$ have a ranking $\sigma_m$ of the
$n$ receivers and each receiver $w$ a ranking $\tau_w$ of the $n$ proposers, where $\sigma_m(k)$
is the choice of $m$ of rank $k$ (rank $0$ is the best) and $\tau_w^{-1}(x)$ is the rank of $x$
for $w$. A state $s$ of deferred acceptance satisfies the invariant when: every proposer has made
at most $n$ proposals; if $w$ holds $m$, then $m$ has made $k + 1$ proposals for some rank $k$
with $\sigma_m(k) = w$; no proposer is held by two different receivers; for every proposer $m$
and every rank $k$ less than the number of proposals of $m$, the receiver $w = \sigma_m(k)$ holds
some $m'$ with $\tau_w^{-1}(m') \le \tau_w^{-1}(m)$; and for such $m$ and $k$, if $\sigma_m(k)$
does not hold $m$, then no perfect matching that is stable for the preferences given by the
rankings matches $m$ with $\sigma_m(k)$.
