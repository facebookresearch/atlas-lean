# Inversion experiment

Let $f$ be a family of functions, $f_n$ mapping $n$-bit strings to bit strings, and let an inverter
map a length $n$, an output and a string of coins to a bit string. The inversion experiment with $m$
coins draws $x \in \{0, 1\}^n$ and $\omega \in \{0, 1\}^m$ uniformly, runs the inverter on
$(n, f_n(x), \omega)$, reads the first $n$ bits of its answer as a string $x'$ (padding with zeros),
and outputs $1$ when $f_n(x') = f_n(x)$. This is the experiment Invert of Katz and Lindell,
Definition 7.1, with a uniform inverter as in Goldreich, Section 2.2.
