# Resource-allocation snapshot

A resource-allocation snapshot, for a type $P$ of
processes and a type $R$ of resources, records for each resource the process holding it, if
any (so each resource has at most one holder), and for each process $p$ and resource $r$
whether $p$ has an outstanding request for $r$. A process never requests a resource it holds.
