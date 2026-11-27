# Kingman's formula is a probability distribution

For natural numbers $1 \le k \le n$, [Kingman's formula](kingman-prob.md) sums to one over the partitions with $k$ blocks:

$$\sum_{\pi \in \mathcal{P}_n,\ |\pi| = k} p_n(\pi) = 1.$$

Equivalently, $\sum_{|\pi| = k} \prod_{B \in \pi} |B|! = n!\,(n-1)!/((n-k)!\,k!\,(k-1)!)$, the Lah number $L(n, k)$.
