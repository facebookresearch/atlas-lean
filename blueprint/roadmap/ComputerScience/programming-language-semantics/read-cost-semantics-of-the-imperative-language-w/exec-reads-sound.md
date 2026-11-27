# The cost of a successful counted run is its number of reads

For every fuel $f$, statement $c$ and states $s$ and $t$: if the read-counting interpreter with fuel $f$ on $c$ from $s$ has outcome $t$, then $c : s \Downarrow^n t$ in the counted big-step semantics, where $n$ is the cost it returns.
