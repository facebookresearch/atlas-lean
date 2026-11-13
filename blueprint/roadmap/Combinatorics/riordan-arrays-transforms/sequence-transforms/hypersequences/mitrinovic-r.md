# Mitrinović's numbers

For complex numbers $a$ and $b$, Mitrinović's numbers
$R^k_j(a, b)$, $j, k \in \mathbb{N}$ (lower index $j$, upper index $k$), are defined by
$R^k_0(a, b) = 1$ if $k = 0$ and $R^k_0(a, b) = 0$ otherwise, and, for all $j, k$, by
$R^0_{j+1}(a, b) = -(a + b j)\, R^0_j(a, b)$ and
$R^{k+1}_{j+1}(a, b) = R^k_j(a, b) - (a + b j)\, R^{k+1}_j(a, b)$.

With $R = 0$ at negative indices this is the recurrence (4.2),
$R^k_j(a, b) = R^{k-1}_{j-1}(a, b) - (a - b + b j)\, R^k_{j-1}(a, b)$ for $j \ge 1$. The start
value is the source's Corollary 5 at $a = 0$ and its solution (4.3) at $j = 0$ for every $a$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*, INTEGERS 26 (2026), Article A36, Section 4, Equation (4.2).
