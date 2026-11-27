# One step of the furthest-in-future manager

Write $x :: L$ for the list $L$ with $x$
prepended, $[\,]$ for the empty list, $|L|$ for the length of $L$, and $L \setminus v$ for $L$
with the first occurrence of $v$ removed. Write $\mathrm{FIF}_k(R, C) = (E, D)$ when the
furthest-in-future manager with capacity $k$ on the requests $R$ from the initial cache $C$ emits
the events $E$ and ends with the cache $D$. Write $\mathrm{hit}(r)$ for a hit on $r$,
$\mathrm{miss}(r)$ for a miss on $r$ with no eviction, and $\mathrm{miss}(r, v)$ for a miss on
$r$ evicting $v$. Let $C$ be a duplicate-free list of blocks with $|C| \le k$, let $r$ be a block
and $f$ a list of blocks, and for a block $b$ let $\nu(b) \in \mathbb{N} \cup \{\infty\}$ be the
position of the first occurrence of $b$ in $f$, or $\infty$ if $b$ does not occur in $f$.
If $r \in C$, then $\mathrm{FIF}_k(r :: f, C) = (\mathrm{hit}(r) :: E, D)$ where
$(E, D) = \mathrm{FIF}_k(f, C)$. If $k = 0$, then
$\mathrm{FIF}_k(r :: f, C) = (\mathrm{miss}(r) :: E, D)$ where $(E, D) = \mathrm{FIF}_k(f, [\,])$.
If $r \notin C$ and $|C| < k$, then $\mathrm{FIF}_k(r :: f, C) = (\mathrm{miss}(r) :: E, D)$
where $(E, D) = \mathrm{FIF}_k(f, r :: C)$. If $r \notin C$, $k > 0$ and $|C| = k$, and $v$ is
the first entry of $C$ at which $\nu$ is maximal on $C$, then
$\mathrm{FIF}_k(r :: f, C) = (\mathrm{miss}(r, v) :: E, D)$ where
$(E, D) = \mathrm{FIF}_k(f, r :: (C \setminus v))$.
