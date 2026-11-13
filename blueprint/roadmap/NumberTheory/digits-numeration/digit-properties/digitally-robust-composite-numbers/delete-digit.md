# Deleting a digit

For natural numbers $N$ and $i$, deleting the base-ten digit of $N$ in
position $i$, where positions are counted from $0$ at the units digit, gives the number

$$\lfloor N / 10^{i+1} \rfloor \cdot 10^{i} + (N \bmod 10^{i}),$$

so the digits above position $i$ move down one place and the digits below position $i$ stay
where they are.

## Sources

- Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
