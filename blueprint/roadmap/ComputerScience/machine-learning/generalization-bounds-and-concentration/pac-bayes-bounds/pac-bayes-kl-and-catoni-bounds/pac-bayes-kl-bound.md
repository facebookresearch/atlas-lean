# Seeger's PAC-Bayes-kl bound for binary losses

For $q, p \in [0,1]$ let $\mathrm{kl}(q\,\|\,p) = q \ln\frac{q}{p} + (1-q)\ln\frac{1-q}{1-p}$ be the binary relative entropy in nats (with $0 \ln 0 = 0$). Let $\Theta$ be a measurable hypothesis space, $\ell : \Theta \times Z \to \{0,1\}$ a jointly measurable binary loss (such as the zero-one loss of a classifier), $P$ a prior probability measure on $\Theta$ fixed before the sample, $D$ a distribution on $Z$, $m \ge 1$ and $\delta \in (0,1)$. With probability at least $1 - \delta$ over $S \sim D^m$, every posterior probability measure $Q$ on $\Theta$ with $\mathrm{KL}(Q\,\|\,P) < \infty$, possibly depending on $S$, satisfies

$$
\mathrm{kl}\big(\mathbb{E}_Q L_S \,\big\|\, \mathbb{E}_Q L_D\big) \le \frac{\mathrm{KL}(Q\,\|\,P) + \ln((m+1)/\delta)}{m}.
$$

If $\Theta$ is countable with every subset measurable, taking point-mass posteriors gives: with probability at least $1 - \delta$ every $i$ with $P(\{i\}) > 0$ satisfies $\mathrm{kl}(L_S(i)\,\|\,L_D(i)) \le (\ln(1/P(\{i\})) + \ln((m+1)/\delta))/m$.

## Proof sketch

For a binary loss, $mL_S(\theta)$ is binomial, so the exponential moment satisfies $\mathbb{E}_S\, e^{m\,\mathrm{kl}(L_S(\theta)\|L_D(\theta))} \le m+1$ for each $\theta$. Tonelli (by joint measurability) and Markov's inequality over the prior give $\mathbb{E}_{\theta \sim P}\, e^{m\,\mathrm{kl}} \le (m+1)/\delta$ with probability $1-\delta$; the Donsker-Varadhan change of measure and joint convexity of $\mathrm{kl}$ (Jensen) move the expectation over $Q$ inside.

## Depends on

- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)

## Sources

- M. Seeger, "PAC-Bayesian Generalisation Error Bounds for Gaussian Process Classification", Journal of Machine Learning Research 3, 2002, Theorem 1.
