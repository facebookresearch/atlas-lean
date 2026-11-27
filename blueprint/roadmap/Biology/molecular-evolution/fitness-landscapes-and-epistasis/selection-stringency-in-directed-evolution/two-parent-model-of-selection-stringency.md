# Two-parent model of selection stringency

**Model.** Two parent variants differ in fitness by $\Delta x > 0$: the fitter has fitness $0$ and the other $-\Delta x$. A budget of $n$ mutants is split into $n_{\mathrm{low}}$ mutants of the less-fit parent and $n - n_{\mathrm{low}}$ of the fitter one. Only beneficial mutations are modelled, with exponential distributions of fitness effects (DFEs): mutants of the fitter parent have fitness $\mathrm{Exp}(\lambda_{\mathrm{high}})$ and mutants of the less-fit parent have fitness $\mathrm{Exp}(\lambda_{\mathrm{low}}) - \Delta x$, all independent. Heterogeneity between the parents' DFEs is modelled by drawing $\lambda_{\mathrm{low}}, \lambda_{\mathrm{high}}$ independently from a common exponential law whose parameter $\alpha$ sets the spread of DFE scales. The outcome is the maximum fitness $M$ of the $n$ mutants; $n_{\mathrm{low}} = 0$ is maximal stringency and $n_{\mathrm{low}} = n/2$ maximal diversification.

**Diminishing returns (Rényi).** If $Y_1, \dots, Y_m$ are i.i.d. $\mathrm{Exp}(\lambda)$, then

$$\mathbb E\big[\max(Y_1, \dots, Y_m)\big] = \frac1\lambda \sum_{i=1}^m \frac1i,$$

so the $i$-th draw from the same DFE raises the expected maximum by only $1/(\lambda i)$.

**Consequences.** If $\lambda_{\mathrm{low}} = \lambda_{\mathrm{high}}$ deterministically, $n_{\mathrm{low}} = 0$ maximizes $M$. With random, independently drawn rates, the less-fit parent's DFE is sometimes more favorable, and because extra draws from the fitter parent's DFE yield only harmonic gains, spending some of the budget on a second DFE can raise the typical maximum despite the $\Delta x$ handicap. The optimal $n_{\mathrm{low}}$ increases with the DFE heterogeneity relative to $\Delta x$ and with the budget $n$, and never exceeds $n/2$ because each parent is equally likely to have the better DFE. Diversification is further favored with more parents, more rounds, and inherited changes in DFEs.

## Depends on

- [Mean of the exponential law](../../../../Probability/distributions/continuous/exponential-distribution/integral-id-exp-measure.md)
- [Harmonic numbers](../../../coalescent-theory/fu-s-branch-length-covariances-for-every-sample/harm.md)

## Proof depends on

- [Competing exponential clocks](../../../../Probability/distributions/continuous/exponential-distribution/competing-exponential-clocks.md)
- [The memoryless property characterizes the exponential law](../../../../Probability/distributions/continuous/exponential-distribution/memoryless-property-characterizes-the-exponential-law.md)

## Expansion

The Rényi representation writes the order statistics of $m$ exponentials as partial sums of independent exponentials with rates $m\lambda, (m-1)\lambda, \dots, \lambda$, so $\max = \sum_{i=1}^m E_i/(i\lambda)$ with $E_i \sim \mathrm{Exp}(1)$, giving the harmonic expectation. Averaged over random rates $\lambda$ the expectation of $M$ can diverge (small $\lambda$ gives heavy tails), so comparisons across $n_{\mathrm{low}}$ are made on $\mathbb E[\log M]$ by simulation. The multi-parent version selects the fittest variant plus $k - 1$ others and splits the $n$ mutants equally; the inheritance version lets each mutant keep its parent's DFE scale except, with some probability, a fixed decrement, and iterates selection of the top $k$ over rounds.

## Sources

- B. A. Alpay and M. M. Desai, "Effects of selection stringency on the outcomes of directed evolution", PLoS ONE 19 (2024), e0311438, Results ("Diversification can help explore heterogeneous DFEs") and Methods ("Two-parent model", "k-parent model", "k-parent inheritance model"), <https://doi.org/10.1371/journal.pone.0311438>, PMCID PMC11472920.
