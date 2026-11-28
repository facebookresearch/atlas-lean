# Lazy random function step

Let the input type $X$ have decidable equality (it need not be finite) and let the range $Y$ be finite and nonempty. A table is a partial function from $X$ to $Y$. One step of the lazy random function at table $T$ and query $x$ is the [lazy sampling step](lazy-step.md) whose fresh answers are uniform on $Y$: if $T$ records $y$ at $x$, it answers $y$ and keeps $T$; otherwise it draws $y$ uniformly from $Y$, answers $y$ and records it at $x$.
