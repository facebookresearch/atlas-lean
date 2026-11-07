# Wall, seed and pre-seed of the Trithoff array via the Tribonacci word

Let
$f_1 < f_2 < \cdots$ be the positive integers whose Tribonacci representation ends in $1$ (the
first column of the Trithoff array). For each row $r \ge 1$ let $\mathrm{out}(f_r)$ and
$\mathrm{out}^2(f_r)$ be the Tribonacci values of the Tribonacci representation of $f_r$,
written most significant digit first, followed by one and by two zeros, that is, with one and
with two new least significant digits $0$. Define, in the integers, the wall
$W_r = \mathrm{out}^2(f_r) - \mathrm{out}(f_r) - f_r$, the seed
$S_r = \mathrm{out}(f_r) - f_r - W_r$ and the pre-seed $P_r = f_r - W_r - S_r$. Count positions
in the infinite Tribonacci word from $1$. Then (i) for every $r \ge 1$, $W_r$ is the $r$-th
position holding $a$ or $b$; (ii) $S_1 = 0$, the seed is non-decreasing in $r$, it takes the
value $0$ exactly once, and it takes each value $m \ge 1$ exactly twice if position $m$ holds
$a$ and exactly once otherwise; and (iii) $P_1 = 0$, the pre-seed is non-decreasing in $r$, it
takes the value $0$ exactly twice, and it takes each value $m \ge 1$ exactly three times if
position $m$ holds $a$ or $b$ and exactly twice if it holds $c$.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Theorem 14 (`jis-2025-25.5.4-thm-14`).
