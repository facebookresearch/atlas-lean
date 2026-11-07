# n-step Lucas numbers

For natural numbers $n \ge 1$ and $m$, the $n$-step Lucas number
$L^{(n)}_m$ is defined by $L^{(n)}_0 = 0$, $L^{(n)}_m = 2^m - 1$ for $1 \le m \le n$, and
$L^{(n)}_m = \sum_{i=1}^{n} L^{(n)}_{m-i}$ for $m \ge n + 1$. For $n = 0$ we set
$L^{(0)}_m = 0$ for every $m$.

The source defines $L^{(n)}_m$ only for $m \ge 1$; the value $L^{(n)}_0 = 0$ is a convention.

## Sources

- <https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex> (source `jis_1628603e2683fb05481e5bfb`, concept `jis_sem_4e0294575601a2b8a5f0d3d7`).
