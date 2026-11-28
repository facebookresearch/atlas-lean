# Mem working Set iff of is Greatest

Suppose $s$ is the greatest process time at or before $t$ when page $p$ was referenced:
there was a reference at $s \le t$ and none to $p$ in $(s,t]$. Then the ideal working-set
policy of width $\tau$ has $p$ resident at $t$ if and only if $t-s\lt \tau$. In particular the
page is absent at equality, even if the process made no intervening references to other pages.
