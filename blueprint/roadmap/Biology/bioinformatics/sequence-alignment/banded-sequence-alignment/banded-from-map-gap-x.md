# Columns using only the first sequence stay in the band

Let $w, i, j \in \mathbb{N}$,
let $x$ be a list of length $n$, and let $A$ be the alignment with one column for each element
$a$ of $x$, in order, with first entry $a$ and empty second entry. If $|i - j| \le w$ and
$|(i + n) - j| \le w$, then the band check of $A$ with width $w$ from offset
$(i, j)$ is true.
