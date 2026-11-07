# Digitally robust composite numbers

A natural number $N$ is a digitally robust composite if
it is composite (greater than $1$ and not prime), coprime to $10$, and each of the following
numbers is greater than $1$ and not prime: the result of replacing the base-ten digit of $N$ in
any position $i$ by any digit $d < 10$ other than $\lfloor N / 10^{i} \rfloor \bmod 10$; the
result of deleting the single digit in any position $i$ smaller than the number of base-ten
digits of $N$; and the result of inserting any digit $d < 10$ in any position $i$. Positions are
counted from $0$ at the units digit, and positions beyond the written digits of $N$ refer to its
leading zeros.

## Sources

- Ian Fultz, Jacob Juillerat, and Aidan Kuster, *Composite Numbers That Remain Composite When Inserting, Replacing, or Deleting a Digit*, INTEGERS 26 (2026), Article A119, Theorem 1.
