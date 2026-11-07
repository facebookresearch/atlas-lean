# Boyer–Moore with the empty pattern

For every text $t$ of length $n$ over the alphabet
$\{0, \dots, \sigma - 1\}$, the Boyer–Moore matcher with the empty pattern and text $t$ returns
the list $0, 1, \dots, n$ of all offsets from $0$ to $n$ in increasing order, at cost $n + 1$.
