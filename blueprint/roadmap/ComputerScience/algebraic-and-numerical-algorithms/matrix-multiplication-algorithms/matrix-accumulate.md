# Square matrix accumulation

Let $\alpha$ be a type with an addition and a multiplication,
and let $A$, $B$, $C$ be $n \times n$ matrices over $\alpha$, stored as vectors of rows. Square
matrix accumulation on $A$, $B$, $C$ is rectangular matrix accumulation on $A$, $B$, $C$ with all
three dimensions equal to $n$: it adds $AB$ to the accumulator $C$ and returns the result with
its cost pair (scalar multiplications, scalar additions).
