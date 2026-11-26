# Randomized menus can earn unboundedly more than deterministic ones for correlated items

For a single additive buyer and two items with correlated values, the ratio between the optimal revenue $\mathrm{REV}$ (over menus of lotteries) and the optimal revenue of deterministic mechanisms (menus of bundles with prices) is unbounded; likewise the ratio $\mathrm{REV}/\max\{\mathrm{SREV}, \mathrm{BREV}\}$ is unbounded, and for every finite menu size $s$ there are distributions requiring menus larger than $s$ for any constant fraction of $\mathrm{REV}$. For independent items, by contrast, the better of selling separately and bundling is a constant-factor approximation.

## Proof sketch

Construct a correlated distribution supported on value vectors of geometrically increasing scales, arranged so that each type is offered a lottery tailored to it whose expected value for the other types is small; deterministic menus cannot separate the types without ceding most of the surplus. A counting argument over menu entries shows that any menu of size $s$ captures only the revenue from $O(s)$ scales, giving the menu-size statement.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)
- [Menu-size complexity of revenue approximation](../menu-size-complexity-of-revenue-approximation.md)

## Proof depends on

- [The better of selling separately and grand bundling is a 6-approximation](max-srev-brev-six-approximation.md)

## Sources

- P. Briest, S. Chawla, R. Kleinberg, S. M. Weinberg, "Pricing lotteries", Journal of Economic Theory 156 (2015); SODA 2010.
- S. Hart, N. Nisan, "The Menu-Size Complexity of Auctions", EC 2013; Journal of Economic Theory (2019), arXiv:1304.6116.
