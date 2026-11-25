# Skip-list search window

Let $k$ be a key and let $H$ be the greatest tower height in a
skip list ($H = 0$ if the list is empty or every tower has height $0$). Start with the full list
of bottom-level nodes, and for each level $i$ from $H - 1$ down to $0$ in turn (no levels when
$H = 0$) replace the current list by the result of advancing at level $i$: within the longest
initial segment of the current list whose keys are all less than $k$, take the last node whose
tower height exceeds $i$ and keep only the nodes after it, leaving the list unchanged if there is
no such node. The search window for $k$ is the list that remains after these steps.
