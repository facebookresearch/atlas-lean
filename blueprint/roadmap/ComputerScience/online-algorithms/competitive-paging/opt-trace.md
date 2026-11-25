# Offline paging trace

Given a cache size $k$, the offline trace from a cache $c$ on a list
of requests is defined by recursion on the list: on the empty list it is empty, and on a list
with first request $p$ and remaining requests $r$ it is the event of the offline step with cache
size $k$ on $c$, $p$ and $r$, followed by the offline trace on $r$ from the new cache of that
step.
