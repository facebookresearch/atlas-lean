# Splitting off a phase

Given a capacity $k$ and a list $s$ of pages (the pages already in
the current phase, most recent first), a request sequence $\sigma$ is split into a phase and a
remainder as follows. The empty sequence splits into two empty parts. For a sequence $p$
followed by $\sigma'$: if $p$ is in $s$, then $p$ joins the phase and $\sigma'$ is split with $s$
replaced by $p$ followed by $s$ with its first occurrence of $p$ removed; if $p$ is not in $s$
and $s$ has fewer than $k$ entries, then $p$ joins the phase and $\sigma'$ is split with $p$
added at the front of $s$; otherwise the phase is empty and the remainder is the whole sequence.

When $s$ has no repetitions and at most $k$ pages, the phase is the longest prefix of $\sigma$
whose distinct pages, together with those of $s$, number at most $k$.
