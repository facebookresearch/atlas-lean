# Predictive parity, error-rate balance and their relations

Calibration within groups and equalized odds are stated on a separate page, listed under the dependencies, with its
conventions for events of probability zero. This node collects the binary-classifier criteria it does not state.

## Expansion

A sound expansion has separate pages for:

1. **Predictive parity:** equal positive predictive value $\Pr(Y = 1 \mid \hat Y = 1, G = g)$ across groups, required only for groups in which
   the predicted-positive event has positive probability.
2. **Error-rate balance:** equal false-positive and false-negative rates across groups, each required only where its conditioning event has
   positive probability.
3. **Relations**, stated as separate implications without identifying the notions: for a binary classifier $\hat Y$, error-rate balance is
   equivalent to equalized odds of $\hat Y$, each rate compared only on groups where its conditioning event has positive probability; and a
   binary classifier calibrated within groups satisfies predictive parity.

## Depends on

- [Group fairness criteria for scores and classifiers](group-fairness-criteria-for-scores-and-classifiers.md)

## Related topics

- [Predictive parity versus error-rate balance](predictive-parity-versus-error-rate-balance.md)

## Sources

- Inherent Trade-Offs in the Fair Determination of Risk Scores — Kleinberg, Mullainathan, Raghavan (arXiv:1609.05807), conditions (A),(B),(C). <https://arxiv.org/pdf/1609.05807>
- Fair prediction with disparate impact — Alexandra Chouldechova (arXiv:1703.00056, ar5iv), Definitions 1-4 and the remark after Definition 2 on binary scores. <https://ar5iv.labs.arxiv.org/html/1703.00056>
- Equality of Opportunity in Supervised Learning — Hardt, Price, Srebro, NeurIPS 2016, Definition 2.1 and its binary reformulation. <https://home.ttic.edu/~nati/Publications/HardtPriceSrebro2016.pdf>
