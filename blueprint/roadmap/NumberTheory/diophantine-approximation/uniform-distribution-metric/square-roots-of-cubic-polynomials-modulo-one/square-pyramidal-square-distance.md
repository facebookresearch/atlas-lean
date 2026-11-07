# Distance from a square pyramidal number to the nearest square

For a natural number
$n$, let $P_n$ be the $n$-th square pyramidal number and $s = \lfloor \sqrt{P_n} \rfloor$. The
distance from $P_n$ to the nearest square is

$$a_n = \min\bigl(P_n - s^2, (s + 1)^2 - P_n\bigr).$$

Since $s^2 \le P_n < (s + 1)^2$, this is $a_n = |P_n - y_n^2|$, where $y_n^2$ is the square
nearest to $P_n$.

No ties occur, since the midpoint $m^2 + m + 1/2$ of two consecutive squares is never an integer.

## Sources

- Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.5.5, equation (a_n first definition) of arXiv:2412.10097v2 (OEIS A351830).
