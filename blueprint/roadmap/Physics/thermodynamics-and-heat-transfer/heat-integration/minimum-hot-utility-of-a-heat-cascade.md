# Minimum hot utility of a heat cascade

Let finitely many temperature intervals, ordered from hot to cold, have widths $w_i > 0$ and sums $H_i, C_i \ge 0$ of the
capacity-flow rates of the hot and cold streams present in them, in compatible units, and put $d_i = w_i (H_i - C_i)$. With a hot
utility $Q \ge 0$ supplied at the top, the heat passed down after the first $k$ intervals is $R_k = Q + \sum_{i<k} d_i$ for
$k = 0, 1, \dots, n$, the last one included. The least $Q \ge 0$ for which every $R_k$ is nonnegative is

$$Q_{\min} = \max\Bigl(0,\ \max_k \bigl(-\textstyle\sum_{i<k} d_i\bigr)\Bigr),$$

the final residual $R_n$ is then the cold utility, and an interval boundary with $R_k = 0$ is a pinch. Only sensible heat is
considered, with no latent heat or losses; synthesizing an exchanger network and targeting area or cost are outside this result.

## Depends on

## Proof depends on

## Sources

- *Process Integration*, NPTEL course 103107094, Module 4, Lecture 13, the problem table algorithm with shifted temperatures and the hot and cold utility targets, <https://archive.nptel.ac.in/content/storage2/courses/103107094/module4/lecture4/lecture4.pdf>.
