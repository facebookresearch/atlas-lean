# Simple tabulation hashing

Split a key $x$ into $c$ characters $x = (x_1, \dots, x_c)$ of $b$ bits each, i.e. $x_i \in \Sigma = [2^b]$. Given $c$ independent uniformly random tables $T_1, \dots, T_c : \Sigma \to [2^M]$, the *simple tabulation* hash is

$$
h(x) = T_1[x_1] \oplus T_2[x_2] \oplus \dots \oplus T_c[x_c],
$$

where $\oplus$ is bitwise exclusive or. It uses $c \cdot 2^b$ words of random tables and $O(c)$ time per evaluation.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- A. L. Zobrist, "A New Hashing Method with Application for Game Playing", Technical Report 88, Computer Sciences Department, University of Wisconsin, 1970.
- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. Patrascu and M. Thorup, "The Power of Simple Tabulation Hashing", Journal of the ACM 59(3), 2012.
