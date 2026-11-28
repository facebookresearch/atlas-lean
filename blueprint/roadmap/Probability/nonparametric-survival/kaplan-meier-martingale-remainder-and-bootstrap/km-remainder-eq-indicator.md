# The exponential-model Kaplan–Meier remainder is a censoring indicator times a constant

Consider the exponential censoring model: the sample space is $\mathbb R$ with the exponential law $\mu_0$ of rate $1$, the failure time is $T(\omega) = \omega$, the censoring time is $C(\omega) = 1$, the survival function is $S(s) = e^{-s}$, and $\Lambda_0$ is the hazard measure of $\mu_0$, $\Lambda_0(B) = \int_B d\mu_0(s) / \mu_0([s, \infty))$ (with $1/0 = \infty$). With the at-risk process $Y(s)(\omega) = \mathbf 1\{s \le T(\omega),\ s \le C(\omega)\}$ and the left limit of the one-subject Kaplan–Meier estimator $\hat S(s-)(\omega) = 1 - \mathbf 1\{T(\omega) \le C(\omega),\ T(\omega) < s\}$, the vanishing-risk remainder is

$$R(t)(\omega) = \int_{(0, t]} \frac{\hat S(s-)(\omega)}{S(s)}\, \mathbf 1\{Y(s)(\omega) = 0\}\, d\Lambda_0(s),$$

a Bochner integral with respect to $\Lambda_0$ (see the [remainder](km-remainder.md) and the [left limit](kaplan-meier-one-left.md)).

Then for every $t \ge 1$ and every $\omega \in \mathbb R$,

$$R(t)(\omega) = \mathbf 1\{\omega > 1\}\,\bigl(e^t - e\bigr).$$

## Sources

- R. D. Gill, Censoring and Stochastic Integrals, Mathematical Centre Tracts 124, Amsterdam (1980), Section 3.2, Lemma 3.2.1(iv), (3.2.12) and (3.2.15)–(3.2.18), pp. 37–38 (the exponential and two-coin formulas are a specialization and a discrete analogue).
