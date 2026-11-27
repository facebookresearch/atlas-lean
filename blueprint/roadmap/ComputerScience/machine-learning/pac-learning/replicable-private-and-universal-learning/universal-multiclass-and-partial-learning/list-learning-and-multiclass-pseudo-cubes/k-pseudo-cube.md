# k-pseudo-cubes and the k-DS dimension

Let $k \ge 1$ and $d \ge 1$. A set $B \subseteq Y^d$ is a **$k$-pseudo-cube of dimension $d$** if it is finite and nonempty and for every $b \in B$ and every coordinate $i \in [d]$ there are at least $k$ vectors $b' \in B \setminus \{b\}$ that agree with $b$ outside coordinate $i$ (so $b$ together with them shows at least $k+1$ distinct labels in coordinate $i$). For $k = 1$ these are the pseudo-cubes of Daniely and Shalev-Shwartz. A tuple $(x_1, \dots, x_d) \in X^d$ is **$k$-DS shattered** by $H \subseteq Y^X$ if the projection $H|_{(x_1,\dots,x_d)}$ contains a $k$-pseudo-cube of dimension $d$, and the **$k$-DS dimension** $d_{k\text{-DS}}(H)$ is the largest such $d$ (or $\infty$). For binary label sets, $1$-pseudo-cubes are exactly the Boolean cubes $\{0,1\}^d$, so the $1$-DS dimension is the VC dimension.

## Sources

- M. Charikar, C. Pabbaraju, "A Characterization of List Learnability", STOC (2023), arXiv:2211.04956, Definition 4.
- N. Brukhim, D. Carmon, I. Dinur, S. Moran, A. Yehudayoff, "A Characterization of Multiclass Learnability", FOCS (2022), arXiv:2203.01550.
- A. Daniely, S. Shalev-Shwartz, "Optimal Learners for Multiclass Problems", COLT (2014), PMLR 35.
