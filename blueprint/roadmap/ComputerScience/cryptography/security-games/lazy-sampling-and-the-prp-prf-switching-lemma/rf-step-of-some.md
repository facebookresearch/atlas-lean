# The lazy random function repeats recorded answers

Let the input type $X$ have decidable equality (it need not be finite) and let the range $Y$ be finite and nonempty. A table is a partial function from $X$ to $Y$. If the table $T$ records the answer $y$ to $x$, one [lazy random function step](rf-step.md) at $T$ and $x$ is the point mass at $(y, T)$: it answers $y$ and leaves $T$ unchanged.
