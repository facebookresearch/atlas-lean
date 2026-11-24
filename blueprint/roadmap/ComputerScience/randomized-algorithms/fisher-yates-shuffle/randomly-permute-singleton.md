# Fisher–Yates on a one-element vector

For every vector $x$ of length $1$ and every draw
history $d$, the Fisher–Yates computation returns $x$ unchanged with cost pair $(1, 1)$: it still
retrieves the single draw $d_0 = 0$ and performs the self-swap at position $0$.
