# Randomized menus can earn unboundedly more than deterministic ones for correlated items

For a single additive buyer and two items with correlated values, the ratio between the optimal revenue $\mathrm{REV}$ (over menus of lotteries) and the optimal revenue of deterministic mechanisms (menus of bundles with prices) is unbounded; likewise the ratio $\mathrm{REV}/\max\{\mathrm{SREV}, \mathrm{BREV}\}$ is unbounded, and for every finite menu size $s$ there are distributions requiring menus larger than $s$ for any constant fraction of $\mathrm{REV}$. For independent items, by contrast, the better of selling separately and bundling is a constant-factor approximation.

## Proof sketch

A menu with $s$ entries earns at most $s \cdot \mathrm{BREV}$, and selling separately and deterministic menus for two items have bounded menu size, so everything follows once $\mathrm{BREV}$ can be a negligible fraction of $\mathrm{REV}$. Construct a correlated two-item distribution supported on value vectors of geometrically increasing scales, arranged so that each type is offered a lottery tailored to it whose value for the other types is small; with values in $[0, 1]^2$ this makes $\mathrm{DREV} < \varepsilon\, \mathrm{REV}$ for any $\varepsilon > 0$, and with unbounded values $\mathrm{REV} = \infty$ while deterministic revenue is $1$.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [The better of selling separately and grand bundling is a 6-approximation](max-srev-brev-six-approximation.md)

## Sources

- P. Briest, S. Chawla, R. Kleinberg, S. M. Weinberg, "Pricing lotteries", Journal of Economic Theory 156 (2015); SODA 2010.
- S. Hart, N. Nisan, "Selling Multiple Correlated Goods: Revenue Maximization and Menu-Size Complexity", Journal of Economic Theory 183 (2019); EC 2013 (as "The Menu-Size Complexity of Auctions"), arXiv:1304.6116, Theorem A.
