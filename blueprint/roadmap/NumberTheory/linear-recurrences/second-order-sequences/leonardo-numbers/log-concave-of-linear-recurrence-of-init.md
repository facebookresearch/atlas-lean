# Log-concavity propagates along a linear recurrence

Let $k \ge 2$ be an integer, let
$c_1, \dots, c_k$ be real numbers with $c_j \ge 0$ for $2 \le j \le k$, and let
$(z_n)_{n \ge 0}$ be a sequence of positive real numbers with

$$z_n = c_1 z_{n-1} - \sum_{j=2}^{k} c_j z_{n-j} \quad (n \ge k).$$

If $z_{i-1} z_{i+1} \le z_i^2$ for $1 \le i < k$, then $z_{n-1} z_{n+1} \le z_n^2$ for every
$n \ge 1$; that is, the whole sequence is log-concave.

The paper assumes that the block $z_0, \dots, z_{k+1}$ is log-concave, which adds the
inequality for $i = k$, and that $c_1 > 0$. Both follow from the other hypotheses: the
recurrence at $n = k + 1$ propagates the inequality for $i = k$ from those for $i < k$, and
the recurrence at $n = k$ forces $c_1 > 0$.

## Sources

- Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 1 (quoted from the paper's reference [17]) (`integers-2024-A82-lem-1`).
