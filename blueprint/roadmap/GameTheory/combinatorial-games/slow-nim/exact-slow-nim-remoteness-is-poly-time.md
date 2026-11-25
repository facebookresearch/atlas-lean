# Theorem 3 (Smith's remoteness of exact slow k-NIM is polynomial-time computable)

The map
sending a list $(x_0, \dots, x_{n-1})$ of natural numbers of length $n$ to Smith's remoteness of
the position $(x_0, \dots, x_{n-1})$ of Slow$A$-Nim on $n$ stacks with $A = \{n - 1\}$ (where
$0 - 1 = 0$) is polynomial-time computable. Here natural numbers, in the input and the output,
are encoded in binary, and a list is encoded as the concatenation of the self-delimiting forms
of the encodings of its entries. For $n = k + 1$ this is the game $\mathrm{NIM}(k + 1, k)$, so $k$
is part of the input.

## Sources

- Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1, Theorem 3.
