# Prophet inequality for k-uniform matroids

For the $k$-uniform matroid (select at most $k$ elements) with independent nonnegative values arriving in an order fixed in advance by the adversary, there is an online policy with $\mathbb{E}[X(S)] \ge \left(1 - \frac{1}{\sqrt{k + 3}}\right)\mathbb{E}[\text{sum of the } k \text{ largest values}]$.

## Proof sketch

Alaei fixes a single threshold $\tau$ with $\sum_i \Pr[X_i > \tau] = k$ and presents each value as a box with probability $x_i = \Pr[X_i > \tau]$ to a $\gamma$-conservative magician holding $k$ wands: the magician opens box $i$ only if the number of wands broken so far (elements selected) is below an adaptively computed threshold, randomizing at the threshold, so that each box is opened with ex-ante probability exactly $\gamma$. For $\gamma \le 1 - 1/\sqrt{k+3}$ the magician never needs more than $k$ wands, and the gambler selects $X_i$ when its box is opened and $X_i > \tau$; comparing with the prophet's sum of the $k$ largest values gives the guarantee.

## Depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Proof depends on

- [An OCRS yields a prophet inequality](ocrs-implies-prophet-inequality.md)

## Sources

- Saeed Alaei, "Bayesian Combinatorial Auctions: Expanding Single Buyer Mechanisms to Many Buyers", SIAM Journal on Computing 43(2) (2014); FOCS (2011), arXiv:1106.0961, Definitions 2–4 and Theorems 4 and 6.
