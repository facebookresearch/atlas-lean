# Distance distribution of a binary code

For a nonempty code $C \subseteq \{0,1\}^n$ its *distance distribution* is $(A_0, \dots, A_n)$ with

$$
A_i = \frac{1}{|C|}\, \#\{(x, y) \in C \times C : d_H(x, y) = i\}.
$$

Then $A_0 = 1$, $A_i \ge 0$, $\sum_i A_i = |C|$, and $C$ has minimum distance at least $d$ if and only if $A_1 = \cdots = A_{d-1} = 0$. For linear codes $A_i$ is the number of codewords of weight $i$.

## Depends on

- [Linear code](../linear-codes/linear-code.md)

## Sources

- Philippe Delsarte, "An algebraic approach to the association schemes of coding theory", Philips Research Reports Supplements 10 (1973).
- F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes", North-Holland (1977).
