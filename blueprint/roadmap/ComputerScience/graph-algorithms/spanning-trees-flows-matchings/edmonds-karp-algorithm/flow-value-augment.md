# Augmenting along a path changes the flow value by the amount

Let $s \ne t$ be vertices,
$f$ a flow, $a$ an integer, and $p$ a nonempty list of vertices whose first entry is $s$ and whose
last entry is $t$. Then the net flow leaving $s$ under the flow obtained by augmenting $f$ along
$p$ by $a$ equals the net flow leaving $s$ under $f$, plus $a$.

No feasibility of $f$, no edge condition on consecutive entries of $p$, and no duplicate-freeness
of $p$ is needed.
