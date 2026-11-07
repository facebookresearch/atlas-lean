# Inserting a digit

For natural numbers $N$, $i$ and $d$, inserting $d$ into the base-ten
expansion of $N$ in position $i$, where positions are counted from $0$ at the units digit, gives
the number

$$\lfloor N / 10^{i} \rfloor \cdot 10^{i+1} + d \cdot 10^{i} + (N \bmod 10^{i}),$$

so the digits in positions $i$ and above move up one place, $d$ takes position $i$, and the
digits below position $i$ stay where they are. For $i = 0$ this appends $d$ on the right, and
for $i$ at least the number of digits of $N$ it inserts $d$ among the leading zeros.

When $i$ equals the number of digits of $N$, inserting $d$ gives the same number as replacing
the first leading zero by $d$.

## Sources

- Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
