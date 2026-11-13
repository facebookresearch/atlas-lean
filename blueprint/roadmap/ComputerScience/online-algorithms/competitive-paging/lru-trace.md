# The LRU trace

Given a capacity $k$, a cache $c$ and a request sequence $\sigma$, the
events LRU emits on $\sigma$ from $c$: nothing on the empty sequence, and on a sequence $p$
followed by $\sigma'$, the event LRU emits when serving $p$ from $c$, followed by the events LRU
emits on $\sigma'$ from the cache after one LRU step with capacity $k$ serving $p$ from $c$.
