# The k-means assignment step is the zero-variance limit of the E-step

Let
$x_1, \dots, x_N$ be points of $\mathbb{R}^d$, let $\mu_1, \dots, \mu_K \in \mathbb{R}^d$ be means
with positive weights $w_1, \dots, w_K$, and let $a$ assign to each $n$ a component $a(n)$ such
that $\|x_n - \mu_{a(n)}\| < \|x_n - \mu_k\|$ for every $k \ne a(n)$. Then $a$ is a nearest-center
assignment, that is, $\|x_n - \mu_{a(n)}\| \le \|x_n - \mu_k\|$ for all $n$ and $k$, and for all
$n$ and $k$ the common-variance responsibility $r_v(x_n, k)$ of component $k$ at $x_n$ for these
weights and means tends to $1$ if $k = a(n)$ and to $0$ otherwise as $v \to 0^+$.
