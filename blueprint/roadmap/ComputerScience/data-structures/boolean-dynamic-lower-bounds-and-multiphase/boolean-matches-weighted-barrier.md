# Boolean dynamic lower bounds reach the weighted $\log^2$ bound

There is an explicit dynamic Boolean data structure problem, obtained by running the inner-product multiphase problem as a dynamic problem (inserting the $x_i$, then the bits of $y$, then querying an index), for which every cell-probe structure with $w = \Theta(\lg n)$ and polylogarithmic update time has query time $\Omega((\lg n/\lg\lg n)^2)$. This matches, for one-bit answers, Larsen's bound for weighted range counting and improves the $\tilde{\Omega}(\lg^{1.5} n)$ bound of Larsen, Weinstein and Yu.

## Proof sketch

Each phase of the multiphase problem is a batch of operations of a dynamic problem whose queries return one bit; with $t_u$ polylogarithmic, the hypothesis $t_u = n^{o(1)}$ of the multiphase bound holds and $\log(t_u w) = O(\log\log n)$.

## Depends on

- [Ko's $\Omega((\log n / \log\log n)^2)$ lower bound for the multiphase problem](multiphase-inner-product-lower-bound.md)
- [The logarithmic barrier for Boolean dynamic problems](boolean-logarithmic-barrier.md)

## Proof depends on

- [Ko's $\Omega((\log n / \log\log n)^2)$ lower bound for the multiphase problem](multiphase-inner-product-lower-bound.md)
- [The logarithmic barrier for Boolean dynamic problems](boolean-logarithmic-barrier.md)

## Sources

- Young Kun Ko, "An Omega((log n / log log n)^2) Cell-Probe Lower Bound for Dynamic Boolean Data Structures", FOCS (2026), arXiv:2603.25914.
- Kasper Green Larsen, Omri Weinstein, Huacheng Yu, "Crossing the Logarithmic Barrier for Dynamic Boolean Data Structure Lower Bounds", STOC (2018); SIAM Journal on Computing (2020), arXiv:1703.03575.
