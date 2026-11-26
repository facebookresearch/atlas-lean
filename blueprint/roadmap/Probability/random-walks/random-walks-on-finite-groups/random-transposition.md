# The random-transposition measure on the symmetric group

Two positions $L$ and $R$ are chosen independently and uniformly among $n$ and the cards there are
swapped (nothing happens when $L = R$). The resulting probability on $S_n$ is

$$T(\mathrm{id}) = \frac1n, \qquad T(\tau) = \frac{2}{n^2} \text{ for each transposition } \tau, \qquad T = 0 \text{ elsewhere}.$$

Here $n \ge 1$. The law after $k$ random transpositions is the convolution power $T^{*k}$.

## Background

- [Fisher–Yates shuffle](../../../ComputerScience/randomized-algorithms/fisher-yates-shuffle/README.md):
  the algorithm with $n - 1$ prescribed transpositions that is exactly uniform; Diaconis and
  Shahshahani's question came from a programmer using $T^{*k}$ instead.

## Sources

- P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*,
  Z. Wahrsch. Verw. Gebiete 57 (1981) 159–179, (1.1) and the remarks of Section 1.
