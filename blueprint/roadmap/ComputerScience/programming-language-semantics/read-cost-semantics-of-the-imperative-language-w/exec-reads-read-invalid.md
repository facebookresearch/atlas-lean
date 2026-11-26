# An out-of-bounds array read costs nothing

Let $x := a[e]$ be a read statement and $s$ a state with $e(s) \ge |a|$, where $|a|$ is the length of $a$. Then for every fuel $f$ the read-counting interpreter with fuel $f$ on the read from $s$ returns failure at cost $0$.
