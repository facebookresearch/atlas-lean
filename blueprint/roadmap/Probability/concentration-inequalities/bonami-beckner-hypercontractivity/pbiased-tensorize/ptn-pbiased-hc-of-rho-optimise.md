# Conditional KKL gives KKL with constant 2 on $(1/2, q)$ for $q \le 1$

Let $q \le 1$ be such that the [conditional KKL statement](ptn-rho-optimise.md) holds at $q$. Then
for every $p \in (1/2, q)$ the KKL inequality with constant $2$ holds at $p$: for every nonempty
finite set $E$ and every $A \subseteq \{0, 1\}^E$, with $f = \mathbf{1}_A$,
$2 \operatorname{Var}_p(f) \log(1 / \max_e \mathrm{Inf}_e(f)) \le \sum_e \mathrm{Inf}_e(f)$.
