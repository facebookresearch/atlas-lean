# Sample median

For $y = (y_1, \dots, y_s) \in \mathbb{R}^s$, the sample median is the least value $y_j$ such that
more than half of the values are at most $y_j$:
$\operatorname{med}(y) = \inf\{y_j : s < 2 \cdot \#\{i : y_i \le y_j\}\}$. For odd $s$ this is the
usual median, for even $s$ the upper of the two middle values, and for $s = 0$ it is $0$ (the
infimum of the empty set is read as $0$).
