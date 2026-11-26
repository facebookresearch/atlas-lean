# A tree-like path is a loop

If $X$ is [tree-like](is-tree-like.md) on $[0, T]$ with $T \ge 0$, then $X_T = X_0$. Indeed the
pair of times $(0, T)$ gives

$$\|X_T - X_0\| \le h(0) + h(T) - 2 \inf_{[0,T]} h = -2 \inf_{[0,T]} h \le 0,$$

because the height function vanishes at both ends and is nonnegative. So a segment with distinct
endpoints is not tree-like, and a tree-like path has zero increment, as its trivial signature
requires at the first level.
