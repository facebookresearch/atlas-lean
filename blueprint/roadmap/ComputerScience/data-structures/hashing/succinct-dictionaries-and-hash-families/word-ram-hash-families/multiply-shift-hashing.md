# Multiply-shift hashing

Let $0 < M \le w_0$. For an odd multiplier $a = 2b + 1$ with $b \in [2^{w_0 - 1}]$, the *multiply-shift* hash function $h_a : [2^{w_0}] \to [2^M]$ is

$$
h_a(x) = \left\lfloor \frac{(a x) \bmod 2^{w_0}}{2^{w_0 - M}} \right\rfloor,
$$

that is, the top $M$ bits of the low $w_0$ bits of $a x$. On a Word RAM with $2 w_0 \le w$ it is evaluated by one multiplication, one mask and one shift, with no overflow.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, "A Reliable Randomized Algorithm for the Closest-Pair Problem", Journal of Algorithms 25(1), 1997, Section 2.2.
