# Correctness of deadlock detection

Let $w$ be the free resource vector and let the list of
pending processes contain no duplicates. A process $p$ is reported by the detection algorithm if
and only if $p$ is pending and no duplicate-free reduction sequence $\sigma$ from $w$ made of
pending processes contains $p$.
