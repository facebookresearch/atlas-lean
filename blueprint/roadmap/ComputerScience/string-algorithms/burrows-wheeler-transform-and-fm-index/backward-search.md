# FM-index backward search

Let $\alpha$ be a linearly ordered alphabet and $\alpha_\bot$ the alphabet $\alpha$ with a new least
letter $\bot$ adjoined. For a list $L$ over $\alpha_\bot$ (the last column of a Burrows–Wheeler
matrix) and a pattern $P$ over $\alpha$, backward search returns a pair $(sp, ep)$ of natural
numbers, read as the half-open row interval $[sp, ep)$. For the empty pattern it returns
$(0, |L|)$. For a pattern $cP'$ with first letter $c$, let $(sp', ep')$ be the result for $P'$;
it returns

$$(C(c) + \mathrm{rank}_c(L, sp'),\ C(c) + \mathrm{rank}_c(L, ep')),$$

where $C(c)$ is the number of letters of $L$ smaller than $c$ and $\mathrm{rank}_c(L, r)$ is the
number of occurrences of $c$ among the first $r$ letters of $L$. The pattern is thus processed
from its last letter to its first, with one step per letter.
