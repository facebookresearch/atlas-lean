# The canonical-path Poincaré inequality

Let $\pi \ge 0$ be weights and $P$ any real matrix on a finite set $S$. Give every ordered pair $x \ne y$ a path $\gamma_{xy}$ from $x$ to $y$, and let $B$ bound every length-weighted edge load by $B$ times the capacity: $\sum_{x \ne y} \pi(x)\pi(y)|\gamma_{xy}| m_{xy}(u,v) \le B\,\pi(u)P(u,v)$ for all $(u,v)$. Then for every $\psi : S \to \mathbb{R}$,

$$\sum_{x,y} (\psi(x)-\psi(y))^2\,\pi(x)\pi(y) \;\le\; B \sum_{x,y} (\psi(x)-\psi(y))^2\,\pi(x)P(x,y).$$

This is the displayed computation in the proof of Theorem 5 of A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370: write $\psi(y)-\psi(x)$ as the telescoping sum of the increments along $\gamma_{xy}$, apply Cauchy–Schwarz along the path (which costs the factor $|\gamma_{xy}|$), and regroup the sum by edges. The inequality needs neither reversibility nor stochasticity; Sinclair attributes the path technique to Diaconis and Stroock (*Annals of Applied Probability* 1 (1991)), whose bound weights the path length differently.
