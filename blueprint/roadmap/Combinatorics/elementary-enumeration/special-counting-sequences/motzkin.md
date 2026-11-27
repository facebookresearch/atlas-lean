# Motzkin number sequence

The Motzkin numbers $(M_n)_{n \ge 0}$ are the natural numbers
defined by $M_0 = 1$ and, for every $n \in \mathbb{N}$,
$M_{n+1} = M_n + \sum_{k=0}^{n-1} M_k M_{n-1-k}$, where the sum is empty when $n = 0$. Thus
$M_0, M_1, M_2, M_3 = 1, 1, 2, 4$.
