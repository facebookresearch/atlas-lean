# McAllester's PAC-Bayes bound with log of root m and its Occam corollary

Let $\Theta$ be a measurable hypothesis space, $\ell : \Theta \times Z \to [0,1]$ jointly measurable, $P$ a prior probability measure on $\Theta$ fixed before the sample, $D$ a distribution on $Z$, $m \ge 2$ and $\delta > 0$. With probability at least $1 - \delta$ over $S \sim D^m$, every posterior probability measure $Q$ on $\Theta$ with $\mathrm{KL}(Q \,\|\, P) < \infty$, possibly depending on $S$, satisfies

$$
\mathbb{E}_{\theta \sim Q} L_D(\theta) \le \mathbb{E}_{\theta \sim Q} L_S(\theta) + \sqrt{\frac{\mathrm{KL}(Q\,\|\,P) + \ln(\sqrt{m}/\delta)}{2(m-1)}}.
$$

For a countable hypothesis index with point-mass posteriors this gives the Occam bound: with probability at least $1-\delta$, every $i$ with $P(\{i\}) > 0$ has $L_D(i) \le L_S(i) + \sqrt{(\ln(1/P(\{i\})) + \ln(m/\delta))/(2(m-1))}$.

## Proof sketch

By Hoeffding's lemma, $\mathbb{E}_S\, e^{2(m-1)(L_D(\theta) - L_S(\theta))^2} \le \sqrt{m}$ for each $\theta$; Tonelli exchanges the prior and sample expectations, and Markov's inequality bounds the prior average by $\sqrt{m}/\delta$ with probability $1 - \delta$. The Donsker-Varadhan change of measure and Jensen's inequality then give $2(m-1)(\mathbb{E}_Q \Delta)^2 \le \mathrm{KL}(Q\|P) + \ln(\sqrt{m}/\delta)$ for all $Q$ simultaneously.

## Depends on

- [PAC-Bayes bound (McAllester form)](../pac-bayes-bound.md)
- [PAC-Bayes bound for finite classes](../pac-bayes-bound-for-finite-classes.md)
- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)

## Proof depends on

- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)

## Sources

- D. A. McAllester, "PAC-Bayesian Model Averaging", Proceedings of the Twelfth Annual Conference on Computational Learning Theory (COLT), ACM, 1999.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
