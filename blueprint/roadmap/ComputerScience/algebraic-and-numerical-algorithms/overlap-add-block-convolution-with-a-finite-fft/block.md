# Blocks of a signal

For natural numbers $N$ and $L$, a signal $x$ of length $N$ and $b \in \mathbb{N}$, block $b$ of $x$ at hop $L$ is the signal $x^{[b]}$ of length $L$ with $x^{[b]}_i = \bar x(bL + i)$, where $\bar x$ is the [zero extension of $x$](../support-bounded-zero-padding-for-cyclic-convolut/extend-nat.md). So block $b$ holds the samples $x_{bL}, \ldots, x_{bL + L - 1}$, with $0$ in place of samples past the end of $x$.
