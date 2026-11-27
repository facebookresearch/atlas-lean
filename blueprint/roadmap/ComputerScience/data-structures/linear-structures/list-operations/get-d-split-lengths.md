# Start position of a chunk in a split list

Let $L$ be a list and $\ell_0, \dots, \ell_{m-1}$ a list of natural numbers. Splitting $L$ at these
lengths cuts consecutive chunks of lengths $\ell_0, \ell_1, \dots$ from the front of $L$, a chunk
being shorter (possibly empty) once $L$ runs out. For every index $i < m$, the $i$-th chunk (counted
from $0$; a default list is returned for indices out of range) is the list of the first $\ell_i$
elements, or all of them if there are fewer, of the list obtained from $L$ by dropping its first
$\ell_0 + \dots + \ell_{i-1}$ elements.
