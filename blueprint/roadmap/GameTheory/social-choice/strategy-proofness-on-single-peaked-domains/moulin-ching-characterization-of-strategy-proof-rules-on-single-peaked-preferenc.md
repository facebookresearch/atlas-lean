# Moulin–Ching characterization of strategy-proof rules on single-peaked preferences

A rule on ordinal single-peaked preferences over $[a, b]$ with finitely many agents is strategy-proof and onto if and only if it is a generalized median voter scheme applied to the reported peaks, i.e. of the form $\max_{S \subseteq N} \min(\beta_S, \min_{i \in S} p_i)$, with the convention $\min_{i \in \emptyset} p_i = b$, for coalition parameters $\beta_S \in [a, b]$ that are monotone ($\beta_S \le \beta_T$ whenever $S \subseteq T$) and satisfy $\beta_\emptyset = a$ and $\beta_N = b$. Every such rule is group strategy-proof in the strong sense.

## Proof sketch

By the peaks-only theorem the rule is a function of peaks, which is a strategy-proof onto facility-location rule on the interval, hence a generalized median voter scheme by Moulin's theorem; the max-min and min-max forms are dual.

## Depends on

- [Ordinal single-peaked preferences on an interval](ordinal-single-peaked-preferences-on-an-interval.md)
- [Generalized median voter scheme on an interval](../../mechanism-design/facility-location-without-money/generalized-median-voter-scheme-on-an-interval.md)

## Proof depends on

- [Option sets are closed intervals; Ching's peaks-only theorem](option-sets-are-closed-intervals-chings-peaks-only-theorem.md)
- [Moulin's characterization of strategyproof location rules on an interval](../../mechanism-design/facility-location-without-money/moulins-characterization-of-strategyproof-location-rules-on-an-interval.md)

## Sources

- James Schummer and Rakesh V. Vohra, "Mechanism Design without Money", Algorithmic Game Theory, Cambridge University Press, 2007.
- Herve Moulin, "On Strategy-Proofness and Single Peakedness", Public Choice, 1980.
- Stephen Ching, "Strategy-proofness and "median voters"", International Journal of Game Theory, 1997.
