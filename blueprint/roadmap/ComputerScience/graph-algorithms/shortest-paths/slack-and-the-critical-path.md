# Slack and the critical path of a project network

Let a project be a finite acyclic directed graph with a source $s$ and a sink $t$, every vertex lying on some $s$–$t$ path, and nonnegative durations $d(e)$ on the arcs (activities); vertices off every $s$–$t$ path are invalid input, not given distance $0$. With $\ell(u, v)$ the length of a longest $u$–$v$ path, the minimum project duration (unlimited resources) is $L = \ell(s, t)$. For a vertex $v$ put $ES(v) = \ell(s, v)$ and $LS(v) = L - \ell(v, t)$; then $LS(v) - ES(v) \ge 0$, with equality exactly when $v$ lies on a longest $s$–$t$ path. For an arc $e = (u, v)$ the total float $TF(e) = LS(v) - ES(u) - d(e)$ satisfies $TF(e) \ge 0$, with equality exactly when $e$ lies on a longest $s$–$t$ path. Zero slack at both endpoints does not make an arc critical: with arcs $s \to t$ of duration $1$ and $s \to v \to t$ of durations $1, 1$, both endpoints of $s \to t$ have slack $0$ but $TF(s \to t) = 1$.

## Sources

- J. E. Beasley, *OR-Notes: Network analysis — activity on arc examples*, Brunel University, worked example, float times, <https://www.brunel.ac.uk/~mastjjb/jeb/or/netmore.html>. The source states a special case or part of the statement; the rest is derived on this page.
