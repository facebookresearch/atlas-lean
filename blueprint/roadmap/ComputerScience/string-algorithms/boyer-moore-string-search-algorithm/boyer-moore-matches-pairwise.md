# Boyer–Moore returns offsets in strictly increasing order

For all words $p$ and $t$ over
the alphabet $\{0, \dots, \sigma - 1\}$, the list of offsets returned by the Boyer–Moore matcher
with pattern $p$ and text $t$ is strictly increasing: each entry is smaller than every entry
after it.
