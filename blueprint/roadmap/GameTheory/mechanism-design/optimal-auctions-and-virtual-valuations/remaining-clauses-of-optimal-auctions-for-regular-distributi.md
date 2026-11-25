# Optimal auctions for regular distributions

The virtual valuation is defined on a separate page, listed under the dependencies. This node collects the
optimal-auction clauses it does not state.

## Expansion

A sound expansion has separate pages for:

1. **Model.** Independent private values $v_i$ with distributions $F_i$ having continuous positive densities on bounded intervals, regular
   (nondecreasing virtual value $\phi_i$), a feasible set of allocations with nonnegative coordinates containing the zero allocation, and a
   tie-breaking rule that keeps the allocation monotone.
2. **Virtual-surplus maximization.** The allocation maximizing $\sum_i \phi_i(v_i) x_i$ pointwise over feasible allocations (allocating nothing
   when every virtual value is negative), with Myerson payments, maximizes expected revenue among dominant-strategy incentive-compatible,
   individually rational mechanisms. Nonnegative coordinates are needed: with the feasible set $\{0, -1\}$ for one bidder with value
   uniform on $[0, 1]$, the maximizer allocates $-1$ below $1/2$, and its Myerson payments leave values above $1/2$ with utility $-1/2$.
3. **Second price with reserve.** For i.i.d. regular values and a single item, the optimal auction is the second-price auction with reserve
   $r = \inf\{v : \phi(v) \ge 0\}$, a threshold defined even when $\phi$ is not invertible at $0$, with the convention that the item is never sold
   when $\phi$ is negative on the whole support.
4. Irregular distributions (ironing) are outside this node.

## Depends on

- [Virtual valuation](virtual-value.md)
- [Single-parameter quasilinear mechanisms: model, DSIC and IR](../myerson-s-lemma-and-revenue-equivalence/remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)

## Proof depends on

- [Myerson's revenue identity (4.10)](integral-payment-mul-density.md)
- [Payment formula](../myerson-s-lemma-and-revenue-equivalence/payment-formula.md)

## Sources

- Optimal Auction Design — Roger B. Myerson, Math. Oper. Res. 6 (1981), Section 5 (optimal auctions in the regular case; the symmetric case is a second-price auction with a reserve). <http://www.cs.princeton.edu/courses/archive/spr08/cos444/papers/myerson81.pdf>
- CS364A Lecture #5: Revenue-Maximizing Auctions — Tim Roughgarden, Stanford University (2013), Section 3.1 (virtual-welfare maximization in single-parameter environments; Definition 3.1 and its nondecreasing relaxation). <http://theory.stanford.edu/~tim/f13/l/l5.pdf>
