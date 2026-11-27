# Convex nondecreasing functions preserve submartingales

Let $\mu$ be a probability measure,
let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration, and let $(X_n)_{n \in \mathbb{N}}$ be a
real-valued submartingale with respect to $(\mathcal{F}_n)$ and $\mu$. Let
$\varphi : \mathbb{R} \to \mathbb{R}$ be convex and nondecreasing, and suppose $\varphi(X_n)$ is
integrable for every $n$. Then $(\varphi(X_n))_{n \in \mathbb{N}}$ is a submartingale with respect
to $(\mathcal{F}_n)$ and $\mu$.

Monotonicity is needed: a convex function of a submartingale need not be a submartingale. For
example, take $\varphi(x) = (x - 4)^2$ and a submartingale with $X_i = 2$ and $X_j = 3$ almost
surely for some $i < j$; then $\varphi(X_i) = 4 > 1 = \varphi(X_j)$.
