# Predictive parity versus error-rate balance

Consider a binary classifier and a group in which the prevalence $p = \Pr(Y = 1)$ lies in $(0, 1)$ and the predicted-positive event has
positive probability, and define $\mathrm{FPR} = \Pr(\hat Y = 1 \mid Y = 0)$, $\mathrm{FNR} = \Pr(\hat Y = 0 \mid Y = 1)$ and
$\mathrm{PPV} = \Pr(Y = 1 \mid \hat Y = 1)$. If $\mathrm{PPV} > 0$, then
$\mathrm{FPR} = \frac{p}{1-p} \cdot \frac{1 - \mathrm{PPV}}{\mathrm{PPV}} \cdot (1 - \mathrm{FNR})$. Hence, if two groups satisfying these
conditions have equal PPV and different prevalences, they cannot have both equal FPR and equal FNR unless $\mathrm{FNR} = 1$ or
$\mathrm{PPV} = 1$ in them. Under these hypotheses $\mathrm{FNR} = 1$ holds exactly when $\mathrm{PPV} = 0$ (no predicted positive is a true
positive), where the identity does not apply, so the two exceptions are a common $\mathrm{PPV}$ of $0$ or $1$. Both occur: with
$\mathrm{PPV} = 1$ both groups have $\mathrm{FPR} = 0$ and may share any value of $\mathrm{FNR}$; with $\mathrm{PPV} = 0$ both have $\mathrm{FNR} = 1$ and
may share a positive $\mathrm{FPR}$. Outside the hypotheses some rate is undefined: $\mathrm{FNR}$ when $p = 0$, $\mathrm{FPR}$ when $p = 1$ and
$\mathrm{PPV}$ when $\Pr(\hat Y = 1) = 0$.

## Related topics

- [Group fairness criteria for scores and classifiers](group-fairness-criteria-for-scores-and-classifiers.md)

## Sources

- A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.3, equation (2.6) and the remark after it; the exceptions $\mathrm{FNR} = 1$ and $\mathrm{PPV} = 1$ are not stated there and follow from (2.6). <https://arxiv.org/pdf/1703.00056>
