# Gaps in the first column of the Trithoff array

Let $f_1 < f_2 < \cdots$ be the positive
integers whose Tribonacci representation ends in the digit $1$ (OEIS A003265, the first column
of the Trithoff array). For every $j \ge 1$ the difference $f_{j+1} - f_j$ is $2$ or $3$, and
$f_{j+1} - f_j = 3$ exactly when $j = p_a(k) + p_b(k)$ for some $k \ge 1$, where $p_a(k)$ and
$p_b(k)$ are the positions, counted from $1$, of the $k$-th occurrences of the letters $a$ and
$b$ in the infinite Tribonacci word.

The paper identifies these sums $p_a(k) + p_b(k)$, that is A003144 + A003145, with A305373.

## Sources

- Eric Chen, Adam Ge, Andrew Kalashnikov, Ella Kim, Evin Liang, Mira Lubashev, Matthew Qian, Rohith Raghavan, Benjamin Taycher, Samuel Wang and Tanya Khovanova, *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Proposition 11 (`jis-2025-25.5.4-prop-11`), https://cs.uwaterloo.ca/journals/JIS/VOL28/Khovanova/khova43.html
