# Partial parking function

Let $s, t \in \mathbb{N}$ and number the $t$ spots
$0, \dots, t-1$. A map $f : \{0, \dots, s-1\} \to \{0, \dots, t-1\}$, giving the preferred spot
of each of $s$ cars, is a partial parking function if for every spot $k \in \{0, \dots, t-1\}$,
at most $t - k$ cars $i$ satisfy $f(i) \ge k$.
