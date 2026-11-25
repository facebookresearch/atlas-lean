# Single-parameter quasilinear mechanisms: model, DSIC and IR

Single-parameter utilities and incentive compatibility for one bidder with fixed opponents on an interval are a
separate page, and dominant-strategy incentive compatibility of a direct mechanism with general types and outcomes is another, both
listed under the dependencies. This node collects only the multi-bidder clauses they do not state.

## Expansion

A sound expansion has separate pages for:

1. **Model.** $n \ge 1$ bidders with private values $v_i \ge 0$, a feasible set $X \subseteq \mathbb{R}^n$ of allocations, an allocation rule
   $x : \mathbb{R}^n_{\ge 0} \to X$, a payment rule $p : \mathbb{R}^n_{\ge 0} \to \mathbb{R}^n$, and utility $v_i x_i(b) - p_i(b)$.
2. **Properties.** Dominant-strategy incentive compatibility for all bidders and all opponent bids (the instance of the general definition
   with types $v_i \ge 0$, outcomes $(x, p)$ and utility $v_i x_i - p_i$, reducing to the interval page for each fixed opponent profile), individual
   rationality (truthful utility nonnegative) and normalization ($p_i(0, b_{-i}) = 0$). Roughgarden's DSIC bundles incentive compatibility with
   nonnegative truthful utility; here the two are separate properties.

## Depends on

- [Incentive compatibility on an interval](is-incentive-compatible-on.md)
- [Dominant-strategy incentive compatibility](../revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Sources

- CS364A Lecture #3: Myerson's Lemma — Tim Roughgarden, Stanford University (2013), single-parameter environment, Sec. 2-4. <http://theory.stanford.edu/~tim/f13/l/l3.pdf>
- CS364A Algorithmic Game Theory Lecture #2: Mechanism Design Basics — Tim Roughgarden, Stanford University (2013), DSIC (Theorem 5.1 and Section 6.3). <http://theory.stanford.edu/~tim/f13/l/l2.pdf>
