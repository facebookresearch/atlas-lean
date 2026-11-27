# Weighted quadratic sum bound for a shared-endpoint kernel

Let $\iota$ be a finite set and $R$ a linearly ordered commutative semiring (for instance $\mathbb{N}$,
$\mathbb{Z}$, $\mathbb{Q}$ or $\mathbb{R}$). Let $c = (c_{ab})_{a, b \in \iota}$ be a symmetric
matrix with entries $c_{ab} \ge 0$ in $R$ whose row sums satisfy $\sum_{b} c_{ab} \le P$ for every
$a$. Let $\kappa(p, q) \in R$, for pairs $p, q \in \iota \times \iota$, be a kernel with
$\kappa(p, q) \le m$ for all $p, q$, where $m \ge 0$, and with $\kappa(p, q) = 0$ whenever $q$ shares
no endpoint with $p$ (that is, $q_1, q_2 \notin \{p_1, p_2\}$). Then

$$
\sum_{p} \sum_{q} c_{p_1 p_2} \, c_{q_1 q_2} \, \kappa(p, q) \le 4P \Bigl(\sum_{a} \sum_{b} c_{ab}\Bigr) m .
$$

The kernel need not be nonnegative or symmetric, and diagonal entries $c_{aa}$ are allowed.
