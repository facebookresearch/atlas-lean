# Steps of the Burrows–Wheeler inversion walk

Let $L$ be a list over a linearly ordered alphabet with a least letter $\bot$ adjoined, and let
$\mathrm{LF}$ be its LF-mapping. For natural numbers $k$ and $r$, the $k$-step inversion walk from
row $r$ is the list $L[r_0], L[r_1], \dots, L[r_{k-1}]$, where $r_0 = r$ and
$r_{i+1} = \mathrm{LF}(r_i)$, and an entry $L[s]$ with $s \ge |L|$ reads as $\bot$. For $k = 0$ it
is empty.
