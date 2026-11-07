# Asymptotics of the roots of a split Thue family

Let $(d, G, \gamma, \delta)$ be a split
Thue recurrence family. Call reals $\alpha_i(n)$ ($i, n \in \mathbb{N}$) an admissible labelling
if there is $N$ such that for all $n \ge N$ and $1 \le i \le d$,
$\prod_{k=1}^{d} (\alpha_i(n) - G_k(n)) = 1$ and $|\alpha_i(n) - G_i(n)| < 1$. Then, first,
there is $N$ such that for all $n \ge N$ every $z \in \mathbb{C}$ with
$\prod_{k=1}^{d} (z - G_k(n)) = 1$ is real; second, an admissible labelling exists; third, for
every admissible labelling $\alpha$ and every $1 \le i \le d$ there are $C \in \mathbb{R}$ and
$N$ such that for all $n \ge N$

$$|(\alpha_i(n) - G_i(n)) \prod_{k \ne i} (G_i(n) - G_k(n)) - 1| \le C \Gamma_i^{-n},$$

where the product is over $1 \le k \le d$ with $k \ne i$, and
$\Gamma_i = \gamma_i^{i-1} (\prod_{k=i+1}^{d-2} \gamma_k) \gamma_d^2$ if $i \le d - 2$ and
$\Gamma_i = \gamma_d^{d-2} |\delta_d|$ otherwise.

## Sources

- Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as Factors*, INTEGERS 25 (2025), Article A35, Lemma 1 (`integers-2025-A35-lem-1`). The `O`-term is written as `|(α⁽ⁱ⁾ - G i n) * ∏_{k ≠ i} (G i n - G k n) - 1| ≤ C * γ_ε⁻ⁿ`; `δ d` enters through its modulus.
