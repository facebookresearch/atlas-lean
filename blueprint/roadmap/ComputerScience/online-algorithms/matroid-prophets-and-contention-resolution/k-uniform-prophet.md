# Prophet inequality for k-uniform matroids

For the $k$-uniform matroid (select at most $k$ elements) with independent values in adversarial order, there is an online policy with $\mathbb{E}[X(S)] \ge \left(1 - \frac{1}{\sqrt{k + 3}}\right)\mathbb{E}[\text{sum of the } k \text{ largest values}]$.

## Proof sketch

Alaei's $\gamma$-conservative magician accepts an element only if it is active under a threshold chosen from the ex-ante relaxation and the current number of selected elements is below a dynamically adjusted random cap; a potential argument on the distribution of the number of selected items shows that each element is offered with probability at least $1 - 1/\sqrt{k+3}$, which then transfers to the value guarantee.

## Depends on

- [Matroid prophet inequality](matroid-prophet-problem.md)

## Proof depends on

- [An OCRS yields a prophet inequality](ocrs-implies-prophet-inequality.md)

## Sources

- Saeed Alaei, "Bayesian Combinatorial Auctions: Expanding Single Buyer Mechanisms to Many Buyers", SIAM Journal on Computing 43(2) (2014); FOCS (2011).
