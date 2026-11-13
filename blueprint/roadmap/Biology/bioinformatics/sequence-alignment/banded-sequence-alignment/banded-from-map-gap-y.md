# Columns using only the second sequence stay in the band

Let $w, i, j \in \mathbb{N}$,
let $y$ be a list of length $n$, and let $A$ be the alignment with one column for each element
$b$ of $y$, in order, with empty first entry and second entry $b$. If $|i - j| \le w$ and
$|i - (j + n)| \le w$, then the band check of $A$ with width $w$ from offset
$(i, j)$ is true.
