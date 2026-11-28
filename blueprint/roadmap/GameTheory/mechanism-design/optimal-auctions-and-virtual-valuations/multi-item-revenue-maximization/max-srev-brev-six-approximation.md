# The better of selling separately and grand bundling is a 6-approximation

For a single additive buyer with independent item values on any number of items,

$$
\mathrm{REV}(D) \le 6 \max\{\mathrm{SREV}(D), \mathrm{BREV}(D)\}.
$$

## Proof sketch

Apply the core-tail decomposition with every threshold equal to $r = \mathrm{SREV}$, so that the tail contributes at most $2\,\mathrm{SREV}$. A one-dimensional distribution with optimal revenue at most $y$ supported on $[0, t y]$ has variance at most $(2t - 1) y^2$, so the core welfare $V = \mathrm{VAL}(D^{\mathrm{core}})$, a sum of independent bounded values, has variance at most $2 r^2$. If $V \le 4r$, then $\mathrm{SREV} \ge V/4$; otherwise Chebyshev's inequality shows that the grand bundle priced at $\tfrac25 V$ sells with probability at least $47/72$, so $\mathrm{BREV} \ge \tfrac{47}{180} V > V/4$. Hence $\mathrm{REV} \le 2\,\mathrm{SREV} + 4 \max\{\mathrm{SREV}, \mathrm{BREV}\}$.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Proof depends on

- [Core-tail decomposition of the optimal revenue](core-tail-decomposition-revenue.md)

## Sources

- M. Babaioff, N. Immorlica, B. Lucier, S. M. Weinberg, "A Simple and Approximately Optimal Mechanism for an Additive Buyer", FOCS 2014; Journal of the ACM 67(4) (2020), arXiv:1405.6146, Theorem 2.
