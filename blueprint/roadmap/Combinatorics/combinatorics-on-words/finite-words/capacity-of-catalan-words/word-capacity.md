# Capacity of a word

The capacity of a word $w = w_1 \cdots w_n$ of natural numbers,
viewed as a bargraph, is

$$\mathrm{cap}(w) = \sum_{i=1}^{n}
\max\Bigl(0, \min\bigl(\max_{j < i} w_j, \max_{j > i} w_j\bigr) - w_i\Bigr),$$

the number of cells of water held above the columns, where an empty maximum is $0$. In particular
the first and last columns hold no water.

## Sources

- Toufik Mansour and Mark Shattuck, *Enumeration of Catalan and Smooth Words According to Capacity*, INTEGERS 25 (2025), Article A5, Section 1, definition of capacity.
