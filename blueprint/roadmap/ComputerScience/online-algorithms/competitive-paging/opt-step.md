# Offline paging step

Given a cache size $k$, a cache $c$ (a list of pages), a requested
page $p$ and the list $f$ of future requests, the offline step returns an event and a new cache.
If $p \in c$, it is a hit on $p$ and the cache is unchanged. Otherwise, if $c$ has fewer than $k$
pages, it is a miss on $p$ with no eviction and the new cache is $p$ followed by $c$. Otherwise,
if some page of $c$ does not occur among the first $k - 1$ entries of $f$ (no entries at all when
$k = 0$, and all of $f$ when $f$ is shorter), it is a miss on $p$ evicting the first such page $v$
in $c$, and the new cache is $p$ followed by $c$ with the first occurrence of $v$ removed. If
there is no such page, it is a miss on $p$ with no eviction and the new cache is $p$ followed by
$c$.
