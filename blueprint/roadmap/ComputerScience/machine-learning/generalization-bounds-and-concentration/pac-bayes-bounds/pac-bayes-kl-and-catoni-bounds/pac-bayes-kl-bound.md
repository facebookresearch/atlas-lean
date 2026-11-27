# Seeger's PAC-Bayes-kl bound for binary losses

For $q, p \in [0,1]$ let $\mathrm{kl}(q\,\|\,p) = q \ln\frac{q}{p} + (1-q)\ln\frac{1-q}{1-p}$ be the binary relative entropy in nats (with $0 \ln 0 = 0$). Let the hypotheses be indexed by a countable set with prior $P$ fixed before the sample, let $\ell(i, z) \in \{0,1\}$ be a measurable binary loss (such as the zero-one loss), $D$ a distribution on $Z$, $m \ge 1$ and $\delta > 0$. With probability at least $1 - \delta$ over $S \sim D^m$, every posterior $Q$ with $\mathrm{KL}(Q\,\|\,P) < \infty$ satisfies

$$
\mathrm{kl}\big(\mathbb{E}_Q L_S \,\big\|\, \mathbb{E}_Q L_D\big) \le \frac{\mathrm{KL}(Q\,\|\,P) + \ln((m+1)/\delta)}{m}.
$$

Taking point-mass posteriors, with probability at least $1 - \delta$ every $i$ with $P(\{i\}) > 0$ satisfies $\mathrm{kl}(L_S(i)\,\|\,L_D(i)) \le (\ln(1/P(\{i\})) + \ln((m+1)/\delta))/m$.

## Proof sketch

For a binary loss, $mL_S(i)$ is binomial, so the exponential moment satisfies $\mathbb{E}_S\, e^{m\,\mathrm{kl}(L_S(i)\|L_D(i))} \le m+1$. Tonelli and Markov's inequality over the prior give $\mathbb{E}_P\, e^{m\,\mathrm{kl}} \le (m+1)/\delta$ with probability $1-\delta$; the Donsker-Varadhan change of measure and joint convexity of $\mathrm{kl}$ (Jensen) move the expectation over $Q$ inside.

## Depends on

- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)

## Proof depends on

- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)

## Sources

- M. Seeger, "PAC-Bayesian Generalisation Error Bounds for Gaussian Process Classification", Journal of Machine Learning Research 3, 2002, Theorem 1.
