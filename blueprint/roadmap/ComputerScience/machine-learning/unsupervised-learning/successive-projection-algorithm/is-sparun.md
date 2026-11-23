# Run of the successive projection algorithm

Let $m_j$ ($j \in \iota$) be vectors in a real inner product space. A finite sequence of picks
$j_1, \dots, j_n \in \iota$ is a run of the successive projection algorithm if each pick
maximizes the [residual](residual.md) norm given the earlier picks: for every $t \le n$ and every
$i \in \iota$, $\|r_{S_{t-1}}(i)\| \le \|r_{S_{t-1}}(j_t)\|$, where $S_{t-1} = \{j_1, \dots, j_{t-1}\}$.
Ties are broken arbitrarily.
