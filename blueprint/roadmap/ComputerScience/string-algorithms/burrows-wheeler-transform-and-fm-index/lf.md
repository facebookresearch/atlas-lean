# LF-mapping from the last column

Let $L$ be a list over a linearly ordered alphabet with a least letter $\bot$ adjoined. For a row
$r$, let $c = L[r]$, read as $\bot$ if $r \ge |L|$. The LF-mapping computed from $L$ alone is

$$\mathrm{LF}(r) = C(c) + \mathrm{rank}_c(L, r),$$

where $C(c)$ is the number of letters of $L$ smaller than $c$ and $\mathrm{rank}_c(L, r)$ is the
number of occurrences of $c$ among the first $r$ letters of $L$.
