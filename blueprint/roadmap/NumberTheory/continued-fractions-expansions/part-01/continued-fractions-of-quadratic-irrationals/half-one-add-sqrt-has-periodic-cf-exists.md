# Parity criterion for $(1 + \sqrt{d})/2$ with a given symmetric period

Let $l \ge 3$ and
let $a_1, \dots, a_{l-1}$ be positive integers with $a_i = a_{l-i}$ for $1 \le i < l$. Let $q_j$ be
the denominator of the $j$-th convergent of $[a_0; a_1, a_2, \dots]$ (so $q_0 = 1$, $q_1 = a_1$ and
$q_{j+2} = a_{j+2} q_{j+1} + q_j$), and let $r_{l-2}$ be the denominator of the $(l-3)$-th
convergent of $[a_1; a_2, a_3, \dots]$. There are natural numbers $d$ and $a_0$ with
$d \equiv 1 \pmod 4$, $d$ not a perfect square, and
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$ if and only if $q_{l-1}$ is
odd, or $q_{l-2}$ and $r_{l-2}$ are odd and $q_{l-1}$ is even.

The restriction $d \equiv 1 \pmod 4$ is needed: $(1 + \sqrt{2})/2 = [1; \overline{4, 1}]$ fits
$l = 6$ with $(a_1, \dots, a_5) = (4, 1, 4, 1, 4)$, where $q_5 = 140$, $q_4 = 29$ and $r_4 = 6$
violate the criterion.

## Sources

- Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and (1 + √D)/2*, INTEGERS 24 (2024), Article A50, Proposition 2 (`integers-2024-A50-prop-2`).
