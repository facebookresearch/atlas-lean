# Capture-safe renaming preserves process scope

Let $n$, $m$ be natural numbers, $f$ a map from names to names sending names scoped at depth $n$ to
names scoped at depth $m$, and $p$ a process scoped at depth $n$. Then the capture-free renaming
$f(p)$ is scoped at depth $m$.
