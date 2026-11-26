# Selection sort

Selection sort of a list $L$ over a linearly ordered type is defined
recursively. If $L$ is empty, the result is the empty list at cost $0$. If $L$ has head $x$ and
tail $L'$, minimum extraction from $L'$ with initial candidate $x$ yields a minimum $m$ and the
list $r$ of remaining elements, and the result is $m$ followed by the selection sort of $r$. The
cost is the sum of the costs of all these minimum extractions.
