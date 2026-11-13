# Two-adic multisection of the power-weighted Lambert series

For every integer $\mu \ge 1$
and every complex number $q$ with $|q| < 1$, the power-weighted Lambert series
$f_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 - q^n)$ and
$g_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 + q^n)$ satisfy

$$
f_\mu(q) = \sum_{j, k \ge 0} 2^{(\mu+1)j+k}
\left(g_\mu\left(q^{2^{j+k}}\right) - 2^{\mu+1} g_\mu\left(q^{2^{j+k+1}}\right)\right),
$$

the sum running over all pairs $(j, k)$ of natural numbers.

The paper prints the weight $2^{2j+k}$, its value for $\mu = 1$ (Corollary 16), which is false
for $\mu \ge 2$: for $\mu = 2$ the coefficient of $q^2$ is $\sigma_2(2) = 1^2 + 2^2 = 5$ on the
left and $1$ on the right. The weight $2^{(\mu+1)j+k}$ is what the paper's proof of Corollary 16
gives with $n^\mu$ in place of $n$: there $2^{2j+k} = 2^{j+k} \cdot 2^j$, where $2^j$ is the
factor of the index $(2n-1) 2^j$ in the summand $n$, which becomes $2^{\mu j}$ for $n^\mu$.

## Sources

- Christophe Vignat and Michael Milgram, *Curious Multisection Identities by Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Corollary 17 (`jis-2024-24.5.5-cor-17`).
