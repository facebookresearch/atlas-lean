# Boyer–Moore returns exactly the occurrences

For all words $p$ and $t$ over the alphabet
$\{0, \dots, \sigma - 1\}$ and every natural number $k$, the offset $k$ belongs to the list
returned by the Boyer–Moore matcher with pattern $p$ and text $t$ if and only if $p$ occurs in
$t$ at offset $k$, that is, $k \le |t|$ and $p$ is a prefix of the word obtained from $t$ by
deleting its first $k$ letters. In particular, overlapping occurrences are all returned.
