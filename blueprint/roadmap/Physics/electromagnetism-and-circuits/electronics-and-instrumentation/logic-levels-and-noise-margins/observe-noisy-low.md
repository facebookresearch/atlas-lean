# Noise below the low margin keeps a low output observed low

Let $V_{ol} < V_{il}$ and let $V_{ih}$ be any real. If an output voltage $y \le V_{ol}$, promised
low, is perturbed by additive noise $e$ with $|e| < V_{il} - V_{ol}$, the low noise margin, then the
[observation](observe.md) of $y + e$ is low, the value `some false`, since $y + e < V_{il}$.
