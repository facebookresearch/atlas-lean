# A fresh lazy query samples a uniform answer and records it

Let the input type $X$ have decidable equality (it need not be finite) and let the range $Y$ be finite and nonempty. A table is a partial function from $X$ to $Y$. If $T$ records no answer at $x$, one [lazy random function step](rf-step.md) at $T$ and $x$ draws $y$ uniformly from $Y$ and returns $y$ together with the table that agrees with $T$ except at $x$, where it records $y$. Only the entry at $x$ changes.
