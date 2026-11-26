# Smoothed online learning is as easy as statistical learning

Let $\mathcal{F}$ be a function class and $\sigma \in (0,1]$. The minimax regret of online learning $\mathcal{F}$ against $\sigma$-smooth adaptive adversaries is bounded, up to logarithmic factors, by the minimax regret against i.i.d. data on a horizon of order $T/\sigma$ (tight bounds hold for nonparametric classes in terms of their entropy, with near-optimal dependence on $T$ and $\sigma$). Moreover there are oracle-efficient algorithms using an empirical risk minimization oracle: an improper algorithm with optimal dependence on $T$, and a proper algorithm making a single oracle call per round whose regret has optimal horizon dependence for classification; both have exponentially worse dependence on $1/\sigma$ than the minimax rate. Every proper oracle-efficient algorithm needs a number of oracle calls polynomially related to this upper bound, which exhibits a statistical-computational gap.

## Proof sketch

By the coupling lemma, each smooth instance is one of $k = O(\log(T)/\sigma)$ i.i.d. proposals from $\mu$, so the adaptive problem embeds into an online problem over a fixed i.i.d. pool of size $Tk$, whose sequential complexity is controlled by the statistical complexity of $\mathcal{F}$ on $Tk$ points. The oracle-efficient algorithms implement follow-the-perturbed-leader with hallucinated samples drawn from $\mu$ as the perturbation, so each round reduces to one ERM call on the history plus the hallucinated data.

## Depends on

- [Coupling smooth sequences with independent samples](smooth-sequence-coupling-lemma.md)
- [Smoothed regret bounds depending on VC dimension and bracketing numbers](smoothed-online-regret-bounds.md)
- [Regularized Follow-the-Leader / Online Mirror Descent regret](../regularized-follow-the-leader-online-mirror-descent-regret.md)

## Proof depends on

- [Coupling smooth sequences with independent samples](smooth-sequence-coupling-lemma.md)
- [Smoothed regret bounds depending on VC dimension and bracketing numbers](smoothed-online-regret-bounds.md)
- [Regularized Follow-the-Leader / Online Mirror Descent regret](../regularized-follow-the-leader-online-mirror-descent-regret.md)

## Sources

- A. Block, Y. Dagan, N. Golowich, A. Rakhlin, "Smoothed Online Learning is as Easy as Statistical Learning", COLT (2022), arXiv:2202.04690.
