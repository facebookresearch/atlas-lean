# The median lies in an interval holding a strict majority

Let $s \in \mathbb{N}$, $y_1, \dots, y_s \in \mathbb{R}$ and $a, b \in \mathbb{R}$. If fewer than half
of the values lie outside $[a, b]$, that is $2 \cdot \#\{i : y_i \notin [a, b]\} < s$, then the
[sample median](sample-median.md) lies in $[a, b]$. This is the deterministic step of the median
trick ("In case this does not happen, the median $Y_i$ supplies a good estimate").

## Sources

- N. Alon, Y. Matias and M. Szegedy, *The space complexity of approximating the frequency
  moments*, Journal of Computer and System Sciences 58 (1999), 137–147, proof of Theorem 2.1.
