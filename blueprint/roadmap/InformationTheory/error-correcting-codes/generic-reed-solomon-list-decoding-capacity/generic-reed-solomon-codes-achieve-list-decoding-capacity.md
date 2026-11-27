# Brakensiek-Gopi-Makam: generic Reed-Solomon codes achieve list-decoding capacity

For all $L \ge 1$, generic Reed-Solomon codes of rate $R$ are $\big(\frac{L}{L+1}(1 - R), L\big)$-list decodable. Consequently, for every $\varepsilon > 0$, with high probability a randomly punctured Reed-Solomon code of rate $R$ over a field of size $q = 2^{O(n)}$ (exponential in the length) is list decodable from radius $1 - R - \varepsilon$ with list size at most $\frac{1 - R - \varepsilon}{\varepsilon}$, resolving a conjecture of Shangguan and Tamo.

## Proof sketch

Generic RS codes are $\mathrm{MDS}(L+1)$, and so are their duals (up to column scaling, generator matrices of generic Reed-Solomon codes), hence they are $\mathrm{LD}$-$\mathrm{MDS}(\le L)$. Choosing $L = \lceil (1 - R - \varepsilon)/\varepsilon \rceil$ gives radius $\frac{L}{L+1}(1-R) \ge 1 - R - \varepsilon$. For each of the at most $2^{O(n)}$ agreement configurations, the bad evaluation tuples lie on the zero set of a nonzero polynomial of degree $\mathrm{poly}(n)$, so by the Schwartz-Zippel lemma and a union bound a random tuple over a field of size $2^{O(n)}$ avoids all of them.

## Depends on

- [Generic and randomly punctured Reed-Solomon codes](generic-reed-solomon-codes.md)

## Proof depends on

- [Generic Reed-Solomon codes are MDS(l) for every l](generic-reed-solomon-codes-are-higher-order-mds.md)
- [Higher order MDS codes attain the generalized Singleton bound](higher-order-mds-implies-generalized-singleton-list-decodability.md)
- [List-decoding capacity, achievability](../list-decoding/exists-encoding-list-decodable.md)
- [List-decoding capacity, converse](../list-decoding/exists-many-in-ball.md)

## Sources

- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256.
