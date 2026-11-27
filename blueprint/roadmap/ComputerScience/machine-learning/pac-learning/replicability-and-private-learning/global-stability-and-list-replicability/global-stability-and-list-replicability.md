# Global stability and list replicability of learning rules

Let $H \subseteq \{0,1\}^X$ and let $A$ map samples of size $n$ to hypotheses.

- $A$ is **$\eta$-globally stable** if for every realizable distribution $D$ there is a hypothesis $h_D$ with $\Pr_{S \sim D^n}[A(S) = h_D] \ge \eta$; the **global stability parameter** $\rho(H)$ is the supremum of $\eta$ such that for every $\varepsilon > 0$ some $\eta$-globally stable learner outputs $h_D$ with error at most $\varepsilon$.
- $A$ is an **$(\varepsilon, L)$-list replicable learner** if for every $\delta > 0$ there is $n$ such that for every realizable $D$ there are hypotheses $h_1, \dots, h_L$, each of error at most $\varepsilon$, with $\Pr_{S \sim D^n}[A(S) \in \{h_1, \dots, h_L\}] \ge 1 - \delta$; the **list replicability number** $\mathrm{LR}(H)$ is the least $L$ such that an $(\varepsilon, L)$-list replicable learner exists for every $\varepsilon > 0$, and $\mathrm{LR}(H) = \infty$ if no finite $L$ works.

Unlike $\rho$-replicability, neither notion lets the two runs share internal randomness. Every finite class satisfies $\rho(H) \ge 1/|H|$ and $\mathrm{LR}(H) \le |H|$; agnostic variants $\rho_{\mathrm{agn}}$ and $\mathrm{LR}_{\mathrm{agn}}$ are defined with excess error in place of error.

## Sources

- M. Bun, R. Livni, S. Moran, "An Equivalence Between Private Classification and Online Prediction", FOCS (2020), arXiv:2003.00563.
- Z. Chase, S. Moran, A. Yehudayoff, "Replicability and Stability in Learning", FOCS (2023), arXiv:2304.03757.
- P. Dixon, A. Pavan, J. Vander Woude, N. V. Vinodchandran, "List and Certificate Complexities in Replicable Learning", NeurIPS (2023), arXiv:2304.02240.
