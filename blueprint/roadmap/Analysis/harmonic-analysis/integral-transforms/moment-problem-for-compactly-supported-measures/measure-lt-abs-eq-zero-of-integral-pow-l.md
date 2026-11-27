# Moment bounds confine the support

Let $\mu$ be a finite measure on $\mathbb{R}$, let $R > 0$ and $C \in \mathbb{R}$, and suppose that
$x \mapsto x^{2k}$ is $\mu$-integrable with $\int x^{2k} \, d\mu \le C R^{2k}$ for every
$k \in \mathbb{N}$. Then $\mu(\{x : |x| > R\}) = 0$.

Proof: for $r > R$, Markov's inequality gives
$\mu(\{|x| \ge r\}) \le r^{-2k} \int x^{2k} \, d\mu \le C (R/r)^{2k} \to 0$ as $k \to \infty$.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, §2.2.3.
