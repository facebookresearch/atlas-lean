# Rouché–Capelli theorem

Let $K$ be a field, let $m$ be a set and $n$ a finite set, let $A$
be an $m \times n$ matrix over $K$, and let $b \in K^m$. Then the linear system $Ax = b$ has a
solution $x \in K^n$ if and only if the rank of $A$ equals the rank of the augmented matrix
$(A \mid b)$, whose columns are the columns of $A$ followed by the single column $b$.

Proof: Following the column-space argument in [Wikipedia, *Rouché–Capelli theorem*,
"Proof"](https://en.wikipedia.org/wiki/Rouch%C3%A9%E2%80%93Capelli_theorem#Proof), solvability is
membership of $b$ in the column span, which we compare before and after adjoining $b$.

## Sources

- https://en.wikipedia.org/wiki/Rouch%C3%A9%E2%80%93Capelli_theorem.
