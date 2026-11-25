# Boyer–Moore agrees with the naive matcher

For all words $p$ and $t$ over the alphabet
$\{0, \dots, \sigma - 1\}$, the list of offsets returned by the Boyer–Moore matcher with pattern
$p$ and text $t$ equals the list returned by the naive matcher with pattern $p$ and text $t$,
entry by entry and in the same order. Only the returned lists are compared, not the costs.
