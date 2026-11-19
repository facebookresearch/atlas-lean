# Optimal auctions and virtual valuations

For a value with continuous positive density $f$ and distribution function $F$ on $[a, b]$, Myerson's virtual valuation is $\varphi(t) = t - (1 - F(t))/f(t)$ (Myerson 1981, (5.1)). Every incentive-compatible mechanism raises expected revenue $\int_a^b P f = \int_a^b \varphi\, Q\, f - U(a)$ (Myerson 1981, (4.10)): revenue is expected virtual surplus, less the utility left to the lowest type. With allocation probabilities in $[0, 1]$ and individual rationality, revenue is at most $\int_a^b \max(\varphi f, 0)$, and when the virtual valuation changes sign once, at a price $r$, the posted price $r$ attains this bound, so it is the optimal mechanism for one bidder (Myerson 1981, §5, with seller value $0$). In Myerson's example of a value uniform on $[0, 100]$, $\varphi(t) = 2t - 100$ and the optimal price $50$ earns $25$. With several bidders, summing the identity over bidders reduces optimal auction design to allocating to the highest nonnegative virtual valuation (Myerson 1981, Lemma 3 and §5, with ironing in §6 when $\varphi$ is not monotone).

- [Virtual valuation](virtual-value.md)
- [Virtual surplus density](virtual-value-mul-density.md)
- [Myerson's revenue identity (4.10)](integral-payment-mul-density.md)
- [Revenue bound from a single bidder](integral-payment-mul-density-le.md)
- [Posted-price allocation](posted-price-alloc.md)
- [Posted-price payment](posted-price-payment.md)
- [Posted-price allocations are monotone](monotone-posted-price-alloc.md)
- [Posted-price payments](posted-price-payment-mul.md)
- [Posted prices are incentive compatible](is-incentive-compatible-on-posted-price.md)
- [Revenue of a posted price](integral-posted-price-payment-mul-densit.md)
- [The optimal mechanism for one bidder](integral-payment-mul-density-le-posted-p.md)

## Related topics

- [Myerson's lemma and revenue equivalence](../myerson-s-lemma-and-revenue-equivalence/README.md): the characterization of incentive-compatible mechanisms used here.
- [Vickrey–Clarke–Groves mechanisms](../vickrey-clarke-groves-mechanisms/README.md): welfare-maximizing rather than revenue-maximizing mechanisms; for symmetric regular bidders the optimal auction is a second-price auction with a reserve price.
