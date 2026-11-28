# Weighted line sums of recurrent double sequences are recurrent

Let $A \colon \mathbb{Z}^2 \to \mathbb{C}$, $b \colon \mathbb{Z} \to \mathbb{C}$, nonzero $\alpha, \beta \in \mathbb{C}$ and positive integers $e_1, e_2$. Suppose:

1. there are $N_1 \in \mathbb{Z}$, $M \in \mathbb{N}$ and complex polynomials $D_1 = \sum_i D_{1,i} X^i$, $D_2 = \sum_l D_{2,l} X^l$ with $D_1(0) \ne 0 \ne D_2(0)$ such that $A(n_1, n_2) = 0$ whenever $n_1 < N_1$ or $n_2 < N_1$, and $\sum_{i, l} D_{1,i} D_{2,l}\, A(N_1 + m_1 - i, N_1 + m_2 - l) = 0$ for all $m_1, m_2 \in \mathbb{N}$ with $m_1 \ge M$ or $m_2 \ge M$ (sums over $0 \le i \le \deg D_1$, $0 \le l \le \deg D_2$);
2. there are $N_2 \in \mathbb{Z}$, $M' \in \mathbb{N}$ and a complex polynomial $E = \sum_i E_i X^i$ with $E(0) \ne 0$ such that $b(m) = 0$ for $m < N_2$ and $\sum_{i} E_i\, b(N_2 + m - i) = 0$ for all $m \ge M'$.

Let $s(t) = \sum_{e_1 n_1 + e_2 n_2 = t} A(n_1, n_2)\, b(n_1)\, \alpha^{n_1} \beta^{n_2}$ (a finite sum, taken as $0$ if infinitely many terms were nonzero). Then there are $N \in \mathbb{Z}$, $M'' \in \mathbb{N}$ and a complex polynomial $F = \sum_i F_i X^i$ with $F(0) \ne 0$ such that $s(t) = 0$ for $t < N$ and $\sum_i F_i\, s(N + m - i) = 0$ for all $m \ge M''$. No coprimality of $e_1, e_2$ is required.
