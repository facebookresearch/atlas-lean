# Interval arithmetic operations

For [intervals](interval.md) $X$ and $Y$ and an operation $\circ \in \{+, -, \times\}$, define

$$X \circ Y = \{x \circ y : x \in X,\ y \in Y\},$$

and, when $0 \notin Y$, $X \div Y = \{x / y : x \in X,\ y \in Y\}$. Each of these sets is again an interval, since it is the image of the compact connected set $X \times Y$ under a continuous map. Explicitly,

$$[a,b] + [c,d] = [a + c,\ b + d], \qquad [a,b] - [c,d] = [a - d,\ b - c],$$

and $[a,b] \times [c,d] = [\min P, \max P]$ for the set $P = \{ac, ad, bc, bd\}$ of endpoint products. Each operation is a set extension of the corresponding real operation: it contains $x \circ y$ for every $x \in X$ and $y \in Y$. Mathlib's `NonemptyInterval` addition and subtraction are defined by the endpoint formulas above; the set-image definitions, the product and the quotient of real intervals are not there.

## Depends on

- [Interval](interval.md)

## Sources

- T. Hickey, Q. Ju and M. H. van Emden, "Interval arithmetic: from principles to implementation", *Journal of the ACM* 48(5):1038–1068, 2001, Section 2.1, Definition 3 (sum, difference and product of real intervals as sets) and Definition 4 (quotient, which for $0 \notin Y$ is the set above); Section 2, Theorem 2 (for nonempty bounded intervals the sum, difference, product, and quotient by an interval not containing $0$, are nonempty bounded intervals); Section 4, Theorem 5 (the product as $[\min P, \max P]$) and the formulas for interval addition and subtraction of bounded intervals in Section 4.5. <https://doi.org/10.1145/502102.502106>
