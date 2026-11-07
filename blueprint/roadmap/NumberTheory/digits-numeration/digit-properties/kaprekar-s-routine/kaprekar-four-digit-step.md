# The four-digit Kaprekar map in difference coordinates

For a base $B$ and a pair of
natural numbers $(d_1, d_2)$, the map $K_B$ forms the list of four digits
$[d_1 - 1, B - 1, B - 1, B - d_1]$ if $d_2 = 0$ and $[d_1, d_2 - 1, B - d_2 - 1, B - d_1]$ if
$d_2 > 0$, sorts it decreasingly as $a_1 \ge a_2 \ge a_3 \ge a_4$, and sets
$K_B(d_1, d_2) = (a_1 - a_4, a_2 - a_3)$. Subtraction of natural numbers is truncated at $0$;
for $1 \le d_1 < B$ and $0 \le d_2 \le d_1$ no truncation occurs.

For such $(d_1, d_2)$ the list holds the digits of the Kaprekar difference (largest minus
smallest arrangement) of any four-digit base-$B$ string with difference coordinates
$(d_1, d_2)$, as in paper displays (5) and (6).

## Sources

- Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, *Four-Digit Kaprekar Dynamics in Odd Bases*, Journal of Integer Sequences 29 (2026), Article 26.4.7, Section 2.1.
