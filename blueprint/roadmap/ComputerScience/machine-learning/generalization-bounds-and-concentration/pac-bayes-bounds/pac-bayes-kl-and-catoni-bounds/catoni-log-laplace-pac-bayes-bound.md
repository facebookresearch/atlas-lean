# Catoni's PAC-Bayes bound with the log-Laplace potential

For $c > 0$ define Catoni's potential $\Phi_c(p) = -\frac{1}{c}\ln\big(1 - p(1 - e^{-c})\big)$ for $p \in [0,1]$; it is convex and strictly increasing with $\Phi_c(p) \le p$, and its inverse is $\Phi_c^{-1}(y) = (1 - e^{-cy})/(1 - e^{-c})$. Let $\Theta$ be any measurable space, $\ell : \Theta \times Z \to [0,1]$ jointly measurable, $P$ a prior probability measure, $m \ge 1$, $c > 0$ and $\delta > 0$. With probability at least $1 - \delta$ over $S \sim D^m$, every posterior $Q$ with $\mathrm{KL}(Q\,\|\,P) < \infty$ satisfies

$$
\Phi_c\big(\mathbb{E}_Q L_D\big) \le \mathbb{E}_Q L_S + \frac{\mathrm{KL}(Q\,\|\,P) + \ln(1/\delta)}{c\,m},
$$

equivalently $\mathbb{E}_Q L_D \le \Phi_c^{-1}\big(\mathbb{E}_Q L_S + (\mathrm{KL}(Q\|P) + \ln(1/\delta))/(cm)\big)$, and hence the linearized bound $\mathbb{E}_Q L_D \le \frac{c}{1-e^{-c}}\mathbb{E}_Q L_S + \frac{\mathrm{KL}(Q\|P) + \ln(1/\delta)}{m(1-e^{-c})}$. In particular every posterior with $\mathbb{E}_Q L_S = 0$ has $\mathbb{E}_Q L_D \le (\mathrm{KL}(Q\,\|\,P) + \ln(1/\delta))/m$, with no logarithmic factor in $m$.

## Proof sketch

For each $\theta$, convexity of $u \mapsto e^{-cu}$ on $[0,1]$ gives $\mathbb{E}_S\, e^{mc(\Phi_c(L_D(\theta)) - L_S(\theta))} \le 1$, with no factor depending on $m$. Integrating over the prior, Markov's inequality, and the Donsker-Varadhan change of measure with Jensen's inequality for the convex $\Phi_c$ give the bound for all posteriors at once. The realizable case cannot take $c \to \infty$ in the linearized form (the high-probability event depends on $c$); instead repeat the argument with $\mathbb{E}_S\, e^{m L_D(\theta)}\mathbf{1}[L_S(\theta) = 0] \le e^{m L_D(\theta)}(1 - L_D(\theta))^m \le 1$ and apply the change of measure to posteriors concentrated on $\{L_S = 0\}$, which are exactly those with $\mathbb{E}_Q L_S = 0$.

## Depends on

- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)
- [Catoni's PAC-Bayes bound](../catoni-pac-bayes.md)

## Proof depends on

- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)

## Sources

- O. Catoni, "PAC-Bayesian Supervised Classification: The Thermodynamics of Statistical Learning", Institute of Mathematical Statistics, 2007.
