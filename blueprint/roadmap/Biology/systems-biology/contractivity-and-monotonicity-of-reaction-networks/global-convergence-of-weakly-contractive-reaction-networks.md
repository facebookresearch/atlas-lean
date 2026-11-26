# Global convergence of weakly contractive reaction networks

**Setting.** Consider a reaction network $\dot x=\Gamma R(x)$ under the standard kinetic assumptions that is weakly contractive on the relative interior of each stoichiometric compatibility class $\mathcal{C}=(x_0+\operatorname{im}\Gamma)\cap\mathbb{R}^n_{\ge0}$, i.e. distinct trajectories strictly approach each other in some norm. The network is *persistent* if no trajectory starting in the positive orthant has an $\omega$-limit point on the boundary.

**Statements.**
1. If a compatibility class contains an equilibrium in its relative interior, that equilibrium is unique and every trajectory of the class, including those starting on the boundary, converges to it (Lemma 12).
2. If the network is persistent, every trajectory converges to a unique equilibrium in the relative interior of its compatibility class (Lemma 14).
3. If the network is reversible, all trajectories of a class converge to at most one equilibrium, which may lie on the boundary (Lemma 16).
4. (Corollary 4.) If the compatibility classes are compact, each contains at least one equilibrium; if the network is moreover persistent or reversible, this equilibrium is unique and globally attracting within its class.

## Depends on

- [Weak contractivity of PND-factorizable reaction networks](weak-contractivity-of-pnd-factorizable-reaction-networks.md)

## Expansion

Weak contractivity extends to non-expansivity on the closure of the class (Lemma 10), so on a compact class the time-$t$ maps act as isometries on the global attractor $\bigcap_{t\ge0}\phi_t(\mathcal{C})$, which contains every $\omega$-limit set. Two distinct interior equilibria would be two trajectories at constant distance, contradicting strict contraction; a trajectory whose $\omega$-limit set is not the equilibrium would likewise keep a positive distance from it. A compact convex forward-invariant set contains an equilibrium by Brouwer's fixed-point theorem (Lemma 17), which gives existence. Persistence pushes the attractor into the interior, and reversibility makes the boundary face carrying a boundary equilibrium forward invariant (Lemma 15), giving uniqueness in both cases.

## Sources

- A. Duvall, M. A. Al-Radhawi, D. D. Jatkar, E. Sontag, "Interplay between Contractivity and Monotonicity for Reaction Networks", arXiv preprint (2024), Section 4, Lemmas 10, 12, 14–17 and Corollary 4, <https://doi.org/10.48550/arXiv.2404.18734>.
