# A computational fuzzy extractor from LWE (decode-then-extract)

Over the Hamming space $\mathbb{Z}_q^m$, let $\mathrm{Gen}(w)$ sample a uniform matrix $A \in \mathbb{Z}_q^{m \times (k+l)}$ and secret $s$, publish $p = (A, As + w)$ and output the first $k$ coordinates of $s$ as the key; $\mathrm{Rep}(w', p)$ subtracts $w'$ and decodes the resulting LWE sample with error $w - w'$ of Hamming weight at most $t$ (for example by trying random subsets of rows). If decision LWE in dimension $l$ holds with the source distribution of the reading $w$ as the error distribution, the scheme is a computationally secure fuzzy extractor: $(s_{1..k}, p)$ is indistinguishable from $(U, p)$.

## Proof sketch

The helper is an LWE sample with the reading as error. Hybrid: replace $As_{k+1..} + w$ by uniform using LWE in dimension $l$ (treating the key part as a known shift), after which the key coordinates are masked by uniform columns and hence independent of the helper.

## Depends on

- [Fuzzy extractor and secure sketch](fuzzy-extractor.md)
- [Learning with errors](../../public-key/hardness-assumptions/learning-with-errors.md)

## Sources

- B. Fuller, X. Meng and L. Reyzin, "Computational Fuzzy Extractors", Information and Computation 275, 2020.
