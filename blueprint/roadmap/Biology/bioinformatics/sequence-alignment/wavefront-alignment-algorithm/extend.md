# Fuelled extension of matches along a diagonal

For sequences $x = x_0 x_1 \cdots$ and $y = y_0 y_1 \cdots$, a diagonal $k$, a natural number $n$ and an offset $h$: with $n = 0$ the result is $h$; with $n + 1$, if $h$ is less than the [largest valid offset](max-offset.md) of $k$ and $x_{h-k} = y_h$, the result is the extension with $n$ from $h + 1$, and otherwise it is $h$.
