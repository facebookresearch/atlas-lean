# Sequential posted-price mechanisms are truthful and approximate prophets

A sequential posted-price mechanism offers bidders in a fixed order take-it-or-leave-it prices $p_i \ge 0$, selling to the first who accepts. With nonnegative prices it is DSIC, individually rational, normalized and weakly group strategyproof: no coalition has a joint misreport under which every member strictly gains. If a bidder whose value equals its price declines, it is also group strategyproof in the strong sense (no joint misreport makes no member worse off and some member strictly better off); if such a bidder accepts, it is not, since that bidder can decline at no cost and let a later coalition member buy. For independent values, the single uniform price equal to half the expected maximum value yields expected welfare at least half the expected maximum value, and posting the maximum of a single independent sample of each value distribution also yields at least half the expected maximum welfare. For independent regular distributions with virtual valuations $\varphi_i$, the prices $p_i = \varphi_i^{-1}(t)$ with $t = \tfrac12\,\mathbb{E}[\max_i \varphi_i(v_i)^+]$ achieve at least half the optimal expected revenue; a matching example shows that fixed-order posted prices cannot beat $1/2$ in general.

## Proof sketch

Each bidder faces a price independent of its own report, which gives truthfulness. For group strategyproofness, a bidder's only options are buying at its own fixed price or nothing; the bidder who buys under truthful reports already gets its better option, and a later bidder can buy only if every earlier bidder who would accept declines, which costs each such bidder $v_i - p_i \ge 0$, a positive amount unless $v_i = p_i$. The welfare bounds are prophet inequalities: with threshold $\tau$, welfare is at least $\tau \Pr[\max \ge \tau] + \sum_i \Pr[\text{nobody before } i \text{ accepts}]\, \mathbb{E}[(v_i - \tau)^+]$, and the stated choices of $\tau$ make this at least half the expected maximum. Revenue follows by applying the argument to virtual values.

## Depends on

- [Single-parameter quasilinear mechanisms: model, DSIC and IR](../myerson-s-lemma-and-revenue-equivalence/remaining-clauses-of-single-parameter-quasilinear-mechanisms.md)
- [Prophet inequality with a single threshold](../../../Probability/martingales/prophet-inequalities/prophet-inequality-with-a-single-threshold.md)

## Proof depends on

- [Critical-bid mechanisms are truthful and coincide with Myerson payments](critical-bid-mechanisms-are-truthful-and-coincide-with-myerson-payments.md)
- [Myerson's revenue identity (4.10)](../optimal-auctions-and-virtual-valuations/integral-payment-mul-density.md)

## Sources

- Shuchi Chawla, Jason D. Hartline, David L. Malec and Balasubramanian Sivan, "Multi-Parameter Mechanism Design and Sequential Posted Pricing", Proceedings of the 42nd ACM Symposium on Theory of Computing (STOC), 2010.
- Aviad Rubinstein, Jack Z. Wang and S. Matthew Weinberg, "Optimal Single-Choice Prophet Inequalities from Samples", 11th Innovations in Theoretical Computer Science Conference (ITCS 2020), 2020.
- Ester Samuel-Cahn, "Comparison of Threshold Stop Rules and Maximum for Independent Nonnegative Random Variables", The Annals of Probability, 1984.
- Tim Roughgarden, "Twenty Lectures on Algorithmic Game Theory", Cambridge University Press, 2016.
