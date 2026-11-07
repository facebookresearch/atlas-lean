# Two's complement value

For a word $w = w_{k-1} \cdots w_0$ of natural numbers,
written with $w_{k-1}$ first, the two's complement value is the integer
$\mathrm{val}_{2c}(w) = \sum_{i\lt k} w_i 2^i - w_{k-1} 2^k$; the empty word has value $0$.
For a binary word (all digits in $\{0, 1\}$) this is the usual two's complement value.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 9.1.
