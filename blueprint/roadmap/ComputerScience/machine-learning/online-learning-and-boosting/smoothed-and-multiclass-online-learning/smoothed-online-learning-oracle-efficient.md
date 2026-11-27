# Smoothed online learning is as easy as statistical learning

Let $\mathcal{F}$ be a function class and $\sigma \in (0,1]$. The minimax regret of online learning a real-valued class $\mathcal{F}$ against $\sigma$-smooth adaptive adversaries is within a factor of order $\log(T/\sigma)$ of the regret in the i.i.d. setting, with bounds in terms of the scale-sensitive VC dimension of $\mathcal{F}$ that are tight in $T$ and $\sigma$ up to logarithmic factors (for classification, $\varepsilon$ average regret after about $d\log(1/\sigma)/\varepsilon^2$ rounds). Moreover there are oracle-efficient algorithms using an empirical risk minimization oracle: an improper relaxation-based algorithm with optimal dependence on $T$ (regret $\sigma^{-1/2}$ times the i.i.d. rate), and a proper follow-the-perturbed-leader algorithm making a single oracle call per round whose regret has optimal horizon dependence for classification and is sublinear in general; both have exponentially worse ($\mathrm{poly}(1/\sigma)$ instead of $\log(1/\sigma)$) dependence on $\sigma$ than the minimax rate. Every proper algorithm with an ERM oracle needs time $\tilde\Omega(\sigma^{-1/2})$, matching the upper bounds up to a polynomial factor, which exhibits a statistical-computational gap.

## Proof sketch

By the coupling lemma, each smooth instance is one of $k = O(\log(T)/\sigma)$ i.i.d. proposals from $\mu$, so the adaptive problem embeds into an online problem over a fixed i.i.d. pool of size $Tk$, whose sequential complexity is controlled by the statistical complexity of $\mathcal{F}$ on $Tk$ points. The improper algorithm instantiates the relaxation method of Rakhlin, Shamir and Sridharan with hallucinated future samples drawn from $\mu$; the proper algorithm is follow-the-perturbed-leader whose perturbation is a Gaussian white noise with intensity approximated by $\mu$, so each round needs a single ERM call on the history plus the perturbation.

## Depends on

- [Smoothed adversaries in online learning](smoothed-adversary.md)

## Proof depends on

- [Coupling smooth sequences with independent samples](smooth-sequence-coupling-lemma.md)

## Sources

- A. Block, Y. Dagan, N. Golowich, A. Rakhlin, "Smoothed Online Learning is as Easy as Statistical Learning", COLT (2022), arXiv:2202.04690, Theorems 3, 7, 10 and 11, Lemma 14.
