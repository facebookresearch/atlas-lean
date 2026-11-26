# Inserting a point into a cycle preserves the number of cycles

Count the cycles of a permutation with each fixed point counted as a cycle of length one. Let $n$ be a natural number, let $e$ be a permutation of $\{0, 1, \dots, n-1\}$, let $q < n$, and let $\tau$ be the permutation of $\{0, 1, \dots, n\}$ with $\tau(0) = q + 1$ and, for $x < n$, $\tau(x+1) = 0$ if $e(x) = q$ and $\tau(x+1) = e(x) + 1$ otherwise; that is, $\tau$ is the copy of $e$ on $\{1, \dots, n\}$ with $0$ inserted into the cycle of $q + 1$ just before $q + 1$. Then $\tau$ has as many cycles as $e$.
