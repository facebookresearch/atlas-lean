# Modular exponentiation

For natural numbers $a$, $b$ and $n$, modular exponentiation with
base $a$, exponent $b$ and modulus $n$ is the recursive procedure that returns $1$ if $b = 0$. If
$b > 0$ is even, it computes the result $d$ for exponent $b/2$ (same base and modulus) and returns
$d \cdot d \bmod n$. If $b$ is odd, it computes the result $d$ for exponent $b - 1$ and returns
$a \cdot d \bmod n$. Each even or odd step performs one multiplication, and the cost of the
procedure is the total number of multiplications performed.

## Sources

- CLRS4 §31.6, printed page 934, `MODULAR-EXPONENTIATION`, with one tick per multiplication.
