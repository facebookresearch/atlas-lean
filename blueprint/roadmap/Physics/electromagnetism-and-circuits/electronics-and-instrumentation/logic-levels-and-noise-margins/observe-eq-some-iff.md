# For $V_{il}<V_{ih}$: low iff $v\le V_{il}$, high iff $v\ge V_{ih}$

Let $V_{il} < V_{ih}$. For each Boolean value $b$, the [observation](observe.md) of a voltage $v$
equals `some b` if and only if either $b$ is false and $v \le V_{il}$, or $b$ is true and
$v \ge V_{ih}$. So $v$ is observed low exactly when $v \le V_{il}$ and high exactly when
$v \ge V_{ih}$, and an observation that is not invalid takes no other value. The ordering is needed:
for $V_{ih} \le V_{il}$ the voltage $v = V_{ih}$ is observed low although $v \ge V_{ih}$.
