# Noise below the high margin keeps a high output observed high

Let $V_{il} < V_{ih} < V_{oh}$. If an output voltage $y \ge V_{oh}$, promised high, is perturbed by
additive noise $e$ with $|e| < V_{oh} - V_{ih}$, the high noise margin, then the
[observation](observe.md) of $y + e$ is high, the value `some true`, since $y + e > V_{ih}$. The
ordering $V_{il} < V_{ih}$ is used: for $V_{ih} \le V_{il}$, a noisy voltage at most $V_{il}$ would
be observed low.
