# VCL trees and the VCL dimension

Let $H \subseteq \{0,1\}^X$. A **VCL tree** (Vapnik–Chervonenkis–Littlestone tree) of depth $d \le \infty$ assigns to each node $u$ at level $k$ a tuple $x_u = (x_u^0, \dots, x_u^k) \in X^{k+1}$, where a node at level $k$ has $2^{k+1}$ children indexed by $y \in \{0,1\}^{k+1}$, such that for every finite path $u_0, u_1, \dots, u_{m}$ from the root (with $u_{i+1}$ the child of $u_i$ labelled $y^{(i)} \in \{0,1\}^{i+1}$) there is $h \in H$ with $h(x_{u_i}^j) = y^{(i)}_j$ for all $i < m$ and $0 \le j \le i$.

The class has an **infinite VCL tree** if there is such a tree with $d = \infty$. Following Bousquet, Hanneke, Moran, Shafer and Tolstikhin, a **$k$-VCL tree** instead assigns a $k$-tuple $x_u \in X^k$ to every node, each node having $2^k$ children indexed by $\{0,1\}^k$, and $H$ shatters it if every finite path is realized in the same sense; the **VCL dimension** $\mathrm{VCL}(H)$ is the largest $k$ such that $H$ shatters an infinite $k$-VCL tree ($0$ if none, $\infty$ if unbounded). A class of finite VC dimension $d$ has no infinite VCL tree, since a node at level $d$ would carry $d+1$ points shattered by $H$; for the same reason $\mathrm{VCL}(H) \le d$, since the root of a $k$-VCL tree shattered by $H$ carries $k$ shattered points.

## Depends on

- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483, Definition 1.8.
- O. Bousquet, S. Hanneke, S. Moran, J. Shafer, I. Tolstikhin, "Fine-Grained Distribution-Dependent Learning Curves", COLT (2023), arXiv:2208.14615, Definitions 2.9, 2.11 and 2.14.
