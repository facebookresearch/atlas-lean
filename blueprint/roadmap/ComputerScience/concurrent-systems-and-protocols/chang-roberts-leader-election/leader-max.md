# Only the maximum is elected

Let $\mathrm{id}$ assign a natural-number identifier, not
necessarily distinct, to each process $0, \dots, n$ of the Chang–Roberts ring. In every state
reachable with these identifiers, if process $i$ has declared itself leader, then
$\mathrm{id}(m) < \mathrm{id}(i)$ for every process $m \ne i$.
