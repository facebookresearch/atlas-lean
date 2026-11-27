# Element distinctness on a logarithmic-cost RAM

On a random-access machine over the natural numbers in which each instruction is charged the bit length of the operands it touches (the logarithmic cost criterion), distinctness of $n$ numbers below $n$ is decidable in cost $O\big((n+1)(\log_2(n+1) + 1)\big)$.

## Proof sketch

The direct-addressing algorithm uses only additions, comparisons and indirect loads and stores of values below $n$; compiling its constant number of registers into the logarithmic-cost RAM charges $O(\log n)$ per instruction.

## Depends on

- [Element distinctness in linear time for a bounded universe](element-distinctness-linear-time.md)

## Proof depends on

- [Element distinctness in linear time for a bounded universe](element-distinctness-linear-time.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
