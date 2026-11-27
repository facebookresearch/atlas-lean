# Extending a scoped name map under a binder keeps it scoped

Let $n$, $m$ be natural numbers and $f$ a map from names to names sending names scoped at depth $n$
to names scoped at depth $m$. Then for every name $a$ scoped at depth $n+1$, $f^{\uparrow}(a)$ is
scoped at depth $m+1$, where $f^{\uparrow}$ is the extension of $f$ under one binder.
