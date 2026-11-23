# The paging adversary

Let $A$ be a deterministic online pager with cache size $k$ on the
$k + 1$ pages $0, \dots, k$. From a state $q$ of $A$, the adversary's sequence of $n$ requests is
empty for $n = 0$; for $n + 1$ it first requests the smallest page not in the cache of $q$ (page
$0$ if there is none) and then continues with the adversary's sequence of $n$ requests from the
state that $A$ reaches from $q$ by serving that request.
