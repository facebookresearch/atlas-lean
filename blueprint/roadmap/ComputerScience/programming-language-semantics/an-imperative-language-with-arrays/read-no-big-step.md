# An out-of-bounds array read has no execution

Let $x := a[e]$ be a read statement and $s$ a state in which the index is out of bounds, $e(s) \ge |a|$, where $|a|$ is the length of $a$. Then there is no state $t$ such that the read takes $s$ to $t$ in the big-step semantics.
