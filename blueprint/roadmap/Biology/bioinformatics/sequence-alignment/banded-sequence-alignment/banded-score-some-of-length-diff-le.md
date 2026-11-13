# The banded score is defined when the lengths are close

Fix a substitution score
$\sigma$, assigning an integer $\sigma(a, b)$ to each pair of letters $a$, $b$, an integer gap
score $g$ and a band width $w \in \mathbb{N}$. If two sequences $x$ and $y$ have lengths differing
by at most $w$, that is $\bigl| |x| - |y| \bigr| \le w$, then the banded alignment score of $x$
and $y$ (for $\sigma$, $g$ and $w$) is defined: it equals some integer $s$.
