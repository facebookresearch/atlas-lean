# The $\sqrt{T}$ regret bound of Hedge

Let $T \ge 1$, $n \ge 2$ and $\ell_1, \dots, \ell_T \in [0, 1]^n$. Hedge with learning rate $\eta = \sqrt{\log n / T}$, started from unit weights, has regret at most $2 \sqrt{T \log n}$ against every expert.

Cesa-Bianchi and Lugosi obtain the sharper $\sqrt{T \log n / 2}$ with $\eta = \sqrt{8 \log n / T}$ through Hoeffding's lemma; that constant is not reached by the argument here. In the language of statistical learning, a regret of order $\sqrt{T \log n}$ is the online counterpart of the $\sqrt{\log \lvert \mathcal{F} \rvert / n}$ deviation of a finite class.

## Informally uses

- [Regret of Hedge for losses in the unit interval](regret-le.md): builds on, with the rate that balances the two terms.

## Background

- [Uniform deviation for a finite class](../../generalization-bounds-and-concentration/finite-class-uniform-deviation.md): the batch analogue of the same $\sqrt{\log(\text{number of experts})}$ dependence.

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, arXiv:1909.05207 (v1–v3 number the second-order bound Theorem 1.5, Section 1.3.3)
- N. Cesa-Bianchi and G. Lugosi, *Prediction, Learning, and Games*, Cambridge University Press (2006), Section 2.2 (the sharper constant).
