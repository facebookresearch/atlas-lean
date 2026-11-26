# The better of selling separately and grand bundling is a 6-approximation

For a single additive buyer with independent item values on any number of items,

$$
\mathrm{REV}(D) \le 6 \max\{\mathrm{SREV}(D), \mathrm{BREV}(D)\}.
$$

## Proof sketch

Apply the core-tail decomposition with thresholds set at the per-item revenue scale $t_j$ determined by $\mathrm{SREV}$, so that the tail contribution is at most $2\,\mathrm{SREV}$. The core values are bounded and independent, so their sum concentrates: its variance is at most a constant times $\mathrm{SREV}^2$, and Chebyshev's inequality shows that pricing the grand bundle slightly below its mean extracts revenue at least the core welfare minus $O(\mathrm{SREV})$. Combining the two bounds yields the constant $6$.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Core-tail decomposition of the optimal revenue](core-tail-decomposition-revenue.md)

## Sources

- M. Babaioff, N. Immorlica, B. Lucier, S. M. Weinberg, "A Simple and Approximately Optimal Mechanism for an Additive Buyer", FOCS 2014; Journal of the ACM 67(4) (2020), arXiv:1405.6146.
