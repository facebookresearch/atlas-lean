# A $\frac{7}{26}(n - 4)^2$ lower bound for Impartial Tak penults

Impartial Tak is the
placement game on the $n \times n$ board whose play ends once the tokens contain a road. For every
$n \ge 5$, every Impartial Tak penult $S$ on the $n \times n$ board satisfies
$7(n - 4)^2 \le 26|S|$, that is, it has at least $\frac{7}{26}(n - 4)^2$ tokens.

## Sources

- the journal text layer prints the bound as `26 (n - 4)2` with the numerator lost; the numerator `7` is the one in arXiv:2408.01837v1, whose statement prints `(7/26)(n - 8)²` but whose proof (summing the Weighted Cross bound of Proposition 13 over the `(n - 4)²` windows, each cell carrying total weight at most `26`) concludes `(7/26)(n - 4)²`, matching the journal's `(n - 4)²`.
- Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025), Article G1, Proposition 14.
