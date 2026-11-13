# Cost bound for the string-matching transition table

For every pattern of length $m$
over the alphabet $\{0, \dots, A-1\}$, the cost of computing its transition table is at most
$2A(m+1)^3$.

The cost counts executed candidates, symbol comparisons, failed decrements and table writes.
