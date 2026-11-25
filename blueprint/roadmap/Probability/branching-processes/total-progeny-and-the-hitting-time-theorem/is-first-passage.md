# First passage of the exploration walk

For $k, n \in \mathbb{N}$, a sequence $x = (x_0, \dots, x_{n-1}) \in \mathbb{N}^n$ is a
first-passage sequence if

$$j < k + \sum_{i < j} x_i \qquad \text{for every } j < n ,$$

that is, the walk $S_j = k + \sum_{i < j} (x_i - 1)$ started at $k$ stays positive at every time
$j < n$. Together with $x_0 + \dots + x_{n-1} + k = n$, which says $S_n = 0$, this means that the
walk first hits $0$ at time $n$.
