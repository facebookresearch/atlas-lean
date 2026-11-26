# Winnow (WINNOW1) for monotone disjunctions

Instances are $x \in \{0,1\}^n$ and targets are monotone disjunctions $x \mapsto \bigvee_{i \in R} x_i$ for $R \subseteq \{1,\ldots,n\}$. WINNOW1 with promotion factor $\alpha > 1$ and threshold $\theta > 0$ keeps weights $w_i \ge 0$, all initially $1$. It predicts $1$ if $\sum_{i : x_i = 1} w_i > \theta$, predicts $0$ if the sum is below $\theta$, and uses a fixed tie rule at equality. Weights change only on mistakes and only for active variables ($x_i = 1$): after a false negative each active weight is multiplied by $\alpha$ (promotion), and after a false positive each active weight is set to $0$ (elimination).

## Depends on

- [Online classification protocol, mistakes and regret](../online-classification-protocol-mistakes-and-regret.md)

## Sources

- Nick Littlestone, "Learning Quickly When Irrelevant Attributes Abound: A New Linear-Threshold Algorithm", Machine Learning 2(4), 1988.
