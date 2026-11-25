# Stochastic linear bandits and LinUCB regret

This node covers the stochastic linear bandit model, the confidence ellipsoid of regularized least squares
and the regret of LinUCB; the elliptical potential bounds used in the regret proof are results of their own.

## Proof depends on

- [Elliptical potential lemma](elliptical-potential-lemma.md)

## Expansion

A sound expansion has separate pages for:

1. **Model.** Stochastic linear bandit with action sets $\mathcal{A}_t \subseteq \mathbb{R}^d$ and rewards
   $X_t = \langle \theta^*, A_t \rangle + \eta_t$ with conditionally 1-sub-Gaussian noise; parameters
   $\lambda > 0$, $d \ge 1$, horizon $n$, $\lVert A_t \rVert \le L$ and $\lVert \theta^* \rVert \le m_2$.
2. **Confidence ellipsoid.** With probability at least $1 - \delta$, for all rounds, $\theta^*$ lies in the ellipsoid of radius
   $\beta_n^{1/2} = \sqrt{\lambda}\, m_2 + \sqrt{2\log(1/\delta) + d \log((d\lambda + nL^2)/(d\lambda))}$ around the
   regularized least-squares estimate (Lattimore and Szepesvári, Theorem 20.5 with Eq. (19.8)).
3. **LinUCB regret.** Under Assumption 19.1 of the source, namely $1 \le \beta_1 \le \dots \le \beta_n$,
   $\langle \theta^*, a - b \rangle \le 1$ for all actions $a, b$ available in the same round, $\lVert a \rVert_2 \le L$, and the
   confidence event of item 2 with probability at least $1 - \delta$, the pseudo-regret
   $\hat R_n = \sum_{t \le n} \max_{a \in \mathcal{A}_t} \langle \theta^*, a - A_t \rangle$ satisfies, with probability at least $1 - \delta$,
   $\hat R_n \le \sqrt{8 d n \beta_n \log((d\lambda + nL^2)/(d\lambda))}$ (Theorem 19.2); with $\delta = 1/n$ the expected regret
   is at most $C d \sqrt n \log(nL)$ for a universal constant $C$ (Corollary 19.3).

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Assumption 19.1, Theorem 19.2, Eq. (19.8), Corollary 19.3, Lemma 19.4 and Theorem 20.5. <https://tor-lattimore.com/downloads/book/book.pdf>
