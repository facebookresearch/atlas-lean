# Reversing the order of summation in the Pascal matrix

For every real number $x$ with
$|x| < 1/2$, writing $\binom{i}{j}$ for the entry of the infinite Pascal matrix in row $i$ and
column $j$, we have
$\sum_{j \ge 0} \sum_{i \ge 0} \binom{i}{j} x^i = \sum_{i \ge 0} \sum_{j \ge 0} \binom{i}{j} x^i$,
and this sum equals $\frac{1}{1 - x} \sum_{j \ge 0} \left(\frac{x}{1 - x}\right)^j$.
