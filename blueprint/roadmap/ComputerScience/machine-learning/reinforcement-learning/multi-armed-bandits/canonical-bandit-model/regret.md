# Regret of a bandit policy

Let $\nu = (P_1, \dots, P_k)$ be a stochastic bandit with $k \ge 1$ arms, whose arm $i$ has mean
$\mu_i = \int x \, dP_i(x)$, let $\mu^* = \max_i \mu_i$ be the largest mean, and let $\pi$ be a policy. The regret of
$\pi$ on $\nu$ over $n$ rounds is

$$R_n = n\mu^* - \mathbb{E}_{\nu,\pi}\Big[\sum_{t \le n} X_t\Big],$$

where the expectation is the integral under the canonical bandit model $\mathbb{P}_{\nu,\pi}$. When the bandit has
finite means, each reward $X_t$ is integrable under $\mathbb{P}_{\nu,\pi}$ and this is the regret of the source.
Otherwise the formula still gives a number, since a Bochner integral of a non-integrable function is $0$, both in the
means and in the expectation.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.4, equation (4.1), under the standing assumption of that section that the means exist and are finite. <https://tor-lattimore.com/downloads/book/book.pdf>
