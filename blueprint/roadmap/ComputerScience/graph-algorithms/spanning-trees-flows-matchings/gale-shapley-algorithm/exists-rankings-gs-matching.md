# Gale-Shapley serves every preference profile with $n$ proposers and $n$ receivers

Let
the $n$ proposers and the $n$ receivers both be numbered $0, \dots, n-1$. Let each proposer $m$
have a strict total order $\lt _m$ of preference on the receivers and each receiver $w$ a strict
total order $\lt _w$ of preference on the proposers, where $x \lt _m y$ means that $m$ prefers $x$ to
$y$, and likewise for $\lt _w$. Then there are permutations $\sigma_m$ (one for each proposer $m$)
and $\tau_w$ (one for each receiver $w$) of $\{0, \dots, n-1\}$, read as rankings, such that
$w \lt _m w'$ exactly when $\sigma_m^{-1}(w) < \sigma_m^{-1}(w')$ and $a \lt _w b$ exactly when
$\tau_w^{-1}(a) < \tau_w^{-1}(b)$, and the Gale-Shapley matching $\mu$ of the rankings $\sigma$
and $\tau$ is stable for these preferences and proposer-optimal: for every perfect matching $\nu$
that is stable for these preferences and every proposer $m$, it is not the case that
$\nu(m) \lt _m \mu(m)$.
