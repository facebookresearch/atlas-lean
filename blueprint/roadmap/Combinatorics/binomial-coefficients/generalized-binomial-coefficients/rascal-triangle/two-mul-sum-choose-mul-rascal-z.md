# Binomial-weighted row sums of the Rascal triangle

For
every natural number $n$, the Rascal numbers
$R_{n,k} = k(n-k) + 1$ ($0 \le k \le n$) satisfy
$2 \sum_{k=0}^{n} \binom{n}{k} R_{n,k} = 2^n \binom{n}{2} + 2^{n+1}$.

The paper prints the exponent $n - 2$ where the correct exponent
is $n - 1$ in $\sum_{k} \binom{n}{k} R_{n,k} = 2^{n-1} \binom{n}{2} + 2^n$
(at $n = 2$ the sum is $6$, not $5$); the identity is stated
doubled so that no exponent is negative at $n = 0$.

## Sources

- Amelia Gibbs and Brian K. Miceli, *Two Combinatorial Interpretations of Rascal Numbers*, J. Integer Seq. 27 (2024), Article 24.8.2, Theorem 10, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Miceli/miceli9.html>.
