# Small-Set Expansion Theorem

Let $A \subseteq \{-1, 1\}^n$ have volume $\alpha = \mathbb{E}[1_A]$. Then for every
$0 \le \rho \le 1$,

$$\mathrm{Stab}_\rho[1_A] = \Pr_{(x, y)\ \rho\text{-correlated}}[x \in A,\ y \in A] \le \alpha^{2/(1+\rho)}.$$

Equivalently, for $\alpha > 0$, $\Pr[y \in A \mid x \in A] \le \alpha^{(1-\rho)/(1+\rho)}$: a
$\rho$-noisy copy of a uniform point of a small set is unlikely to stay in the set. The noisy
hypercube is a small-set expander. Here $1_A$ may be any function with values in $\{0, 1\}$, the indicator of the set where it is $1$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Small-Set Expansion Theorem, Section 9.5 (the case $\rho = 1/3$ is Corollary 9.8 in
  Section 9.2).
