# The all-keys predicate is unchanged by erasing height caches

For a predicate $p$ on keys
and a tree $t$ with cached heights, $\mathrm{All}(p, t)$ holds if and only if $p$ holds at every
key of the plain binary tree obtained from $t$ by erasing its cached heights. This holds by
definition.
