# Length-weighted load versus load

Let $S$ be a finite set, $\pi : S \to \mathbb{R}$ with $\pi(x) \ge 0$ for every $x$, and for each
ordered pair $(x, y)$ let $\gamma_{xy}$ be a path from $x$ (the list of states it visits after
$x$). If $|\gamma_{xy}| \le \ell$ for all $x \ne y$, then for every oriented edge $(u, v)$ the
[length-weighted load](elongated-path-load.md) is at most $\ell$ times the [load](path-load.md):

$$\sum_{x \ne y} \pi(x)\pi(y)\, |\gamma_{xy}|\, m_{xy}(u, v) \le \ell \sum_{x \ne y} \pi(x)\pi(y)\, m_{xy}(u, v),$$

where $m_{xy}(u, v)$ is the number of times $\gamma_{xy}$ uses $(u, v)$. This is the observation
behind Sinclair's Corollary 6.

## Sources

- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
  Combinatorics, Probability and Computing 1 (1992), 351–370, Corollary 6.
