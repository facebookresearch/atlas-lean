# Banach–Saks theorem for uniformly convex spaces

Let $E$ be a uniformly convex real Banach
space and let $(x_n)_{n \in \mathbb{N}}$ be a bounded sequence in $E$. Then there are a strictly
increasing map $\varphi : \mathbb{N} \to \mathbb{N}$ and a point $y \in E$ such that the Cesàro
means $\frac{1}{n} \sum_{i=0}^{n-1} x_{\varphi(i)}$ converge to $y$ in norm as $n \to \infty$.

## Sources

- S. Banach and S. Saks, Studia Math. 2 (1930) 51-57; uniformly convex form and property due to Kakutani, 1939; textbook Diestel, Sequences and Series in Banach Spaces; Lean gives uniformly convex real Banach specialization with explicit `StrictMono φ` and norm-convergent Cesàro means.
