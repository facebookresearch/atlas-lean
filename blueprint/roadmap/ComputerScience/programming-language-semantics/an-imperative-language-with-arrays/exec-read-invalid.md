# The interpreter fails on an out-of-bounds array read

Let $x := a[e]$ be a read statement and $s$ a state with $e(s) \ge |a|$, where $|a|$ is the length of $a$. Then for every fuel $f$ the interpreter with fuel $f$ fails on the read from $s$; it never supplies a default value.
