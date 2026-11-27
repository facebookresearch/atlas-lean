# Every lazy answer is recorded and the table grows

Let the input type $X$ have decidable equality (it need not be finite) and let the range $Y$ be finite and nonempty. A table is a partial function from $X$ to $Y$. For every table $T$, query $x$ and pair $(y, T')$ in the support of one [lazy random function step](rf-step.md) at $T$ and $x$: the new table records the answer, $T'(x) = y$, and $T'$ extends $T$ (every answer recorded in $T$ is recorded in $T'$ with the same value).
