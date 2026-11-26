# Binary search for the last index whose key is at most a value

For keys $k(i)$ in a linear
order, a value $x$ and indices $lo \le hi$, the search returns $lo$ when $lo \ge hi$; otherwise it
compares $k(m) \le x$ at $m = \lfloor (lo + hi + 1)/2 \rfloor$, charging one unit, and continues on
$[m, hi]$ if it holds and on $[lo, m - 1]$ otherwise.
