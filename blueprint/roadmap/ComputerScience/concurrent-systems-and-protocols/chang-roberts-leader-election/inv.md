# The Chang–Roberts invariant

Given identifiers $\mathrm{id}$ on a ring of $n + 1$
processes, a state satisfies the invariant when two conditions hold. First, for every message
from origin $j$ waiting in the channel of process $k$, every process $m \ne j$ that the message
has already passed has a smaller identifier, $\mathrm{id}(m) < \mathrm{id}(j)$; here $m$ has been
passed when its forward distance from $j$ is less than the distance the message has travelled,
which is the forward distance from $j$ to $k$ if $k \ne j$, and $n + 1$ (the whole ring) if
$k = j$. Second, for every leader $i$ and every process $m \ne i$, we have
$\mathrm{id}(m) < \mathrm{id}(i)$.
