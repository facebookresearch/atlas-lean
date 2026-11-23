# Replicated genotype matrix of a template block

For natural numbers $g$, $k$ and $b$ and a real $g \times k$ template matrix $T$, the replicated
matrix is the real $b g \times b k$ matrix whose entry for individual $(u, r)$, with $u < b$ and
$r < g$, and marker $(u', a)$, with $u' < b$ and $a < k$, is $\sqrt{b}\, T_{ra}$ if $u = u'$ and $0$
otherwise; individual $(u, r)$ has index $u g + r$ and marker $(u', a)$ has index $u' k + a$. It
consists of $b$ copies of $T$, each on its own cohort of $g$ individuals, rescaled by $\sqrt{b}$.
