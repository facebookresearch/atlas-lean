# Positive predictive value of diagnostic parameters

For real parameters $(\pi, \mathrm{se}, \mathrm{sp})$ (prevalence, sensitivity and specificity), the
positive predictive value is

$$
\mathrm{PPV}(\pi, \mathrm{se}, \mathrm{sp}) =
\frac{\pi\, \mathrm{se}}{\pi\, \mathrm{se} + (1 - \pi)(1 - \mathrm{sp})},
$$

a real ratio with the convention $x / 0 = 0$: it is $0$ when the denominator vanishes, for example
at $\pi = 0$, $\mathrm{sp} = 1$. For $\pi, \mathrm{se}, \mathrm{sp} \in [0, 1]$ with a positive
denominator, the denominator is the probability of a positive test and the ratio is the probability
of disease given a positive test (Bayes' formula).
