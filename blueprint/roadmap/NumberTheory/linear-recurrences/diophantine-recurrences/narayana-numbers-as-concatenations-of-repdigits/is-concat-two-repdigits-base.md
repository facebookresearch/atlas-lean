# Concatenations of two repdigits in a general base

A natural number $n$ is a
concatenation of two repdigits in base $b$ if there are digits $a_1, a_2$ with
$1 \le a_1 \le b - 1$, $0 \le a_2 \le b - 1$ and $a_1 \ne a_2$, and block lengths $l, m \ge 1$,
such that $(b - 1) n = a_1 (b^l - 1) b^m + a_2 (b^m - 1)$. The digit conditions force
$b \ge 2$, and the equation says that the base-$b$ expansion of $n$ is $l$ copies of $a_1$
followed by $m$ copies of $a_2$.

Because of the condition $a_1 \ne a_2$, a repdigit such as $4 = (11)_3$ is not a concatenation
of two repdigits in base $3$. For $b = 10$ this is the notion of a concatenation of two decimal
repdigits.

## Sources

- Prasanta Kumar Ray and Kisan Bhoi, *Narayana Numbers Which Are Concatenations of Two Base b Repdigits*, INTEGERS 24 (2024), Article A20, Section 1 (Equation (1)).
