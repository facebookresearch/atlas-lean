# Lock compatibility at a point

A locked schedule $s$ is legal just before position $p$
when, for every data item $x$, all distinct transactions $t \ne t'$ and all lock modes $m$, $m'$:
if $t$ holds a lock on $x$ covering $m$ and $t'$ holds a lock on $x$ covering $m'$ just before
position $p$ of $s$, then $m$ and $m'$ are both the shared mode. In words, two transactions do not
both hold locks on the same item unless both locks are shared.
