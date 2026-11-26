# Lucas-balancing numbers (shifted indexing)

The shifted sequence $(L_n)_{n \ge 0}$ has
$L_0 = 3$, $L_1 = 1$ and $L_{n+2} = 6L_{n+1} - L_n$.

Section 1 of Mohapatra, Bhoi and Panda defines the standard sequence by $C_0 = 1$, $C_1 = 3$
and the same recurrence. Thus `lucasBalancingNum (n + 1)` equals $C_n$ for every $n \ge 0$.
Their Theorem 3 lists the shifted values $L_2 = 3$ and $L_3 = 17$.

## Sources

- Monalisa Mohapatra, Pritam Kumar Bhoi, and Gopal Krishna Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3.
