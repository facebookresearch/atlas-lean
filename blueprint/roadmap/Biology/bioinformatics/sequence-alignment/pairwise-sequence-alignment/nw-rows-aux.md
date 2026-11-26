# Row-by-row filling of the Needleman–Wunsch table

For a sequence $y$, a sequence $x$ and a row $r$: if $x$ is empty the result is $r$, and for $x = a x'$ the result is that for $x'$ starting from the [next row](next-row.md) of $r$ for $a$ and $y$.
