# Boolean dynamic lower bounds reach the weighted $\log^2$ bound

There is an explicit dynamic Boolean data structure problem, the multiphase problem for inner product over $\mathbb{F}_2$ with $k = n^{1 + \Omega(1)}$ (preprocess $x_1, \dots, x_k$, then apply the bits of $y$ as $n$ single-bit updates, then query an index), for which every cell-probe structure with $w = \Theta(\lg n)$ and polylogarithmic update time has query time $\Omega((\lg n/\lg\lg n)^2)$. This matches, for one-bit answers, Larsen's bound for weighted range counting and improves the $\tilde{\Omega}(\lg^{1.5} n)$ bound of Larsen, Weinstein and Yu.

## Proof sketch

Each phase of the multiphase problem is a batch of operations of a dynamic problem whose queries return one bit. With $t_u$ polylogarithmic and $w = \Theta(\lg n)$, the hypothesis $t_u = n^{o(1)}$ of Ko's bound holds and $\log(t_u w) = O(\log\log n)$, so $t_{tot} = \Omega((\log n/\log(t_u w))^2) = \Omega((\log n/\log\log n)^2)$.

## Depends on

- [Pătraşcu's multiphase problem](multiphase-problem.md)
- [Amortized update and query cost of a dynamic cell-probe structure](../dynamic-information-transfer-lower-bounds/amortized-cell-probe-costs.md)

## Proof depends on

- [Ko's $\Omega((\log n / \log\log n)^2)$ lower bound for the multiphase problem](multiphase-inner-product-lower-bound.md)

## Sources

- Young Kun Ko, "An Omega((log n / log log n)^2) Cell-Probe Lower Bound for Dynamic Boolean Data Structures", FOCS (2026), arXiv:2603.25914.
- Kasper Green Larsen, Omri Weinstein, Huacheng Yu, "Crossing the Logarithmic Barrier for Dynamic Boolean Data Structure Lower Bounds", STOC (2018); SIAM Journal on Computing (2020), arXiv:1703.03575.
