# The weighted log-likelihood is bounded by its value at the normalized counts

Let $Z$ be
a finite set, let $c \colon Z \to \mathbb{R}$ be nonnegative counts with positive total
$C = \sum_{z \in Z} c_z > 0$, and let $w \colon Z \to \mathbb{R}$ be positive weights with
$\sum_{z \in Z} w_z = 1$. Then $\sum_{z \in Z} c_z \log w_z \le \sum_{z \in Z} c_z \log(c_z / C)$
(Gibbs' inequality).

When every count is positive the normalized counts $c_z / C$ are themselves admissible weights,
so they maximize.
