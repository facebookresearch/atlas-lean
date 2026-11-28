# McAllester's PAC-Bayes bound with log of root m and its Occam corollary

Let $\Theta$ be a measurable hypothesis space, $\ell : \Theta \times Z \to [0,1]$ jointly measurable, $P$ a prior probability measure on $\Theta$ fixed before the sample, $D$ a distribution on $Z$ and $\delta \in (0,1)$. Each of the following holds with probability at least $1 - \delta$ over $S \sim D^m$, for every posterior probability measure $Q$ on $\Theta$ with $\mathrm{KL}(Q \,\|\, P) < \infty$, possibly depending on $S$:

1. if $m \ge 2$,

    $$
    \mathbb{E}_{\theta \sim Q} L_D(\theta) \le \mathbb{E}_{\theta \sim Q} L_S(\theta) + \sqrt{\frac{\mathrm{KL}(Q\,\|\,P) + \ln(m/\delta)}{2(m-1)}};
    $$

2. if $m \ge 8$,

    $$
    \mathbb{E}_{\theta \sim Q} L_D(\theta) \le \mathbb{E}_{\theta \sim Q} L_S(\theta) + \sqrt{\frac{\mathrm{KL}(Q\,\|\,P) + \ln(2\sqrt{m}/\delta)}{2m}}.
    $$

For a countable hypothesis index with point-mass posteriors, item 1 gives the Occam bound: for $m \ge 2$, with probability at least $1-\delta$, every $i$ with $P(\{i\}) > 0$ has $L_D(i) \le L_S(i) + \sqrt{(\ln(1/P(\{i\})) + \ln(m/\delta))/(2(m-1))}$.

## Proof sketch

Item 1: with $\Delta(\theta) = L_D(\theta) - L_S(\theta)$, Hoeffding's inequality gives $\mathbb{E}_S\, e^{2(m-1)\Delta(\theta)^2} \le m$ for each $\theta$; Tonelli exchanges the prior and sample expectations, and Markov's inequality bounds the prior average by $m/\delta$ with probability $1 - \delta$. The Donsker-Varadhan change of measure and Jensen's inequality then give $2(m-1)(\mathbb{E}_Q \Delta)^2 \le \mathrm{KL}(Q\|P) + \ln(m/\delta)$ for all $Q$ simultaneously. Item 2: for $m \ge 8$ the binary relative entropy satisfies $\mathbb{E}_S\, e^{m\,\mathrm{kl}(L_S(\theta)\|L_D(\theta))} \le 2\sqrt{m}$, so the same change of measure, with joint convexity of $\mathrm{kl}$, gives $\mathrm{kl}(\mathbb{E}_Q L_S \,\|\, \mathbb{E}_Q L_D) \le (\mathrm{KL}(Q\|P) + \ln(2\sqrt m/\delta))/m$, and binary Pinsker $\mathrm{kl}(q\|p) \ge 2(p-q)^2$ gives item 2.

Sharper constant in item 1: Hoeffding's lemma bounds the moment generating function of $\Delta(\theta)$, and averaging $e^{\lambda \Delta}$ over a Gaussian $\lambda$ gives $\mathbb{E}_S\, e^{2(m-1)\Delta(\theta)^2} \le (1 - (m-1)/m)^{-1/2} = \sqrt{m}$, so the same argument proves item 1 with $\ln(\sqrt{m}/\delta)$ in place of $\ln(m/\delta)$.

## Depends on

- [PAC-Bayes bound (McAllester form)](../pac-bayes-bound.md)
- [PAC-Bayes bound for finite classes](../pac-bayes-bound-for-finite-classes.md)
- [Donsker–Varadhan variational formula](../../../../../InformationTheory/information-inequalities/donsker-varadhan-variational-formula/kl-div-eq-i-sup.md)

## Proof depends on

- [Binary Pinsker inequality on the closed interval](../../../../../InformationTheory/information-inequalities/binary-pinsker-of-mem-icc.md)

## Sources

- D. A. McAllester, "PAC-Bayesian Model Averaging", Proceedings of the Twelfth Annual Conference on Computational Learning Theory (COLT), ACM, 1999.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Theorem 31.1.
- A. Maurer, "A Note on the PAC Bayesian Theorem", arXiv:cs/0411099, 2004, Theorem 5.
- P. Alquier, "User-friendly Introduction to PAC-Bayes Bounds", Foundations and Trends in Machine Learning 17(2), 2024, Section 3.2.2.
