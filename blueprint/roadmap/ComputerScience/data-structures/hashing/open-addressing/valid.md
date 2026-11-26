# Valid open-addressing tables

Let $T$ be an open-addressing table with $m$ slots and probe
sequence $p$, where $p(k, i) \in \{0, \dots, m - 1\}$ is the slot visited by the $i$-th probe of
key $k$. Then $T$ is valid when it satisfies two conditions. Probe-closedness: whenever slot $j$
holds a binding $k \mapsto v$, there is an $i < m$ with $p(k, i) = j$ such that the slots
$p(k, i')$ are occupied for all $i' < i$; this is what lets a lookup stop at the first empty
slot. Key uniqueness: if slots $j_1$ and $j_2$ hold bindings with the same key $k$, then
$j_1 = j_2$; so each key has at most one binding and insertion genuinely replaces it.
