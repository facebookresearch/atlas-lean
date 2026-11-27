# Predictive parity versus error-rate balance

Consider a binary classifier and a group, and model the group by the joint law of the label $Y$ and the prediction $\hat Y$ in it, a
probability measure on $\{0, 1\} \times \{0, 1\}$; every rate below depends on the classifier and the group only through this law. Suppose
that the prevalence $p = \Pr(Y = 1)$ lies in $(0, 1)$ and that the predicted-positive event has positive probability, and define the
conditional probabilities $\mathrm{FPR} = \Pr(\hat Y = 1 \mid Y = 0)$, $\mathrm{FNR} = \Pr(\hat Y = 0 \mid Y = 1)$ and
$\mathrm{PPV} = \Pr(Y = 1 \mid \hat Y = 1)$. If $\mathrm{PPV} > 0$, then
$\mathrm{FPR} = \frac{p}{1-p} \cdot \frac{1 - \mathrm{PPV}}{\mathrm{PPV}} \cdot (1 - \mathrm{FNR})$. Hence, if two groups satisfying these
conditions have equal PPV and different prevalences, they cannot have both equal FPR and equal FNR unless $\mathrm{FNR} = 1$ or
$\mathrm{PPV} = 1$ in them. Under these hypotheses $\mathrm{FNR} = 1$ holds exactly when $\mathrm{PPV} = 0$ (no predicted positive is a true
positive), where the identity does not apply, so the two exceptions are a common $\mathrm{PPV}$ of $0$ or $1$. Both occur, at any
prevalences: $\mathrm{PPV} = 1$ forces $\mathrm{FPR} = 0$, and for every $p \in (0, 1)$ and $f \in [0, 1)$ some group satisfying the
hypotheses has prevalence $p$, $\mathrm{PPV} = 1$ and $\mathrm{FNR} = f$; $\mathrm{PPV} = 0$ forces $\mathrm{FNR} = 1$, and for every
$p \in (0, 1)$ and $r \in (0, 1]$ some group satisfying the hypotheses has prevalence $p$, $\mathrm{PPV} = 0$ and $\mathrm{FPR} = r$. So two
groups of different prevalences may share $\mathrm{PPV} = 1$, $\mathrm{FPR} = 0$ and any $\mathrm{FNR}$ in $[0, 1)$, or $\mathrm{PPV} = 0$,
$\mathrm{FNR} = 1$ and any $\mathrm{FPR}$ in $(0, 1]$.

Outside the hypotheses the conditioning event of some rate has probability zero, so that rate is undefined: $\mathrm{FNR}$ when $p = 0$,
$\mathrm{FPR}$ when $p = 1$ and $\mathrm{PPV}$ when $\Pr(\hat Y = 1) = 0$. The definitions then give it the value $0$, as conditioning on an
event of probability zero gives the zero measure, and the statement makes no claim there.

## Related topics

- [Group fairness criteria for scores and classifiers](group-fairness-criteria-for-scores-and-classifiers.md)

## Sources

- A. Chouldechova, *Fair prediction with disparate impact: A study of bias in recidivism prediction instruments*, arXiv:1703.00056v1 (Big Data 5(2), 2017), §2.3: the identity is equation (2.6), and the remark after it states the impossibility without its exceptions. The exceptions follow from (2.6) and the definitions of the rates; that $\mathrm{FNR} = 1$ exactly when $\mathrm{PPV} = 0$, and that $\mathrm{PPV} = 1$ forces $\mathrm{FPR} = 0$, follow from the definitions; and the groups showing that both exceptions occur are built from explicit cell probabilities. None of these is stated there. <https://arxiv.org/pdf/1703.00056>
