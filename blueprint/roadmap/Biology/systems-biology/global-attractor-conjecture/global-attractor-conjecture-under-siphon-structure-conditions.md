# Global attractor conjecture under siphon structure conditions

**Setting.** Let $\mathcal N$ be a weakly reversible, complex-balanced mass-action reaction network on $m$ species, $x_0 > 0$, and $x^*$ the unique positive complex-balanced equilibrium in the stoichiometric compatibility class of $x_0$. A *siphon* $\Sigma$ is a set of species such that every reaction producing a species of $\Sigma$ consumes one; the face $\{x_\Sigma = 0\}$ is then invariant. Write $x = (z, s)$ with $z = x_\Sigma$. Reactions whose reactant and product contain no species of $\Sigma$ are *$\Sigma$-blind*; they span the stoichiometric space $S_{\mathrm{bl}}(\Sigma)$ of the face dynamics. Let $S_0(\Sigma) = \{v : (0, v) \in \widetilde S\}$ be the stoichiometric directions internal to the face. Projecting reactions onto the vanishing species and freezing $s = b$ gives the *embedded network* $\mathcal N_\Sigma(b)$; its active linkage classes $L_\ell$ have stoichiometric spaces $S_\ell$, and $L_\ell$ is *$\Sigma$-minimal* if it contains a componentwise-minimal active embedded complex. Condition $(\diamond)$: $S_\ell \cap \mathbb R^{|\Sigma|}_{\ge 0} \ne \{0\}$ for every $\Sigma$-minimal $L_\ell$. Let $\mathcal S(x_0)$ be the set of siphons that can be zero sets of $\omega$-limit points of $x_0$.

**Theorem.** Assume that for every $\Sigma \in \mathcal S(x_0)$:
- (a) $S_0(\Sigma) = S_{\mathrm{bl}}(\Sigma)$ (in particular if a compatibility class meets the face $z = 0$ in at most one point), and
- (b) condition $(\diamond)$ holds for the embedded network.

Then $x(t) \to x^*$ as $t \to \infty$.

Intermediate results: under (a) alone, either $x(t) \to x^*$ or $x(t)$ converges to a single boundary equilibrium $(0, b)$, $b > 0$, whose zero set is a siphon; and for a single active embedded linkage class $(\diamond)$ holds automatically.

## Depends on

- [The pseudo-Helmholtz function does not increase along solutions](../complex-balancing-and-the-deficiency-zero-theore/antitone-on-pseudo-helmholtz.md)

## Expansion

By the Siegel–MacLean dichotomy, the $\omega$-limit set of a positive trajectory of a complex-balanced system is either $\{x^*\}$ or a set of boundary equilibria. Condition (a) makes each compatibility class contain at most one boundary equilibrium with a given zero set; finiteness of possible zero sets and connectedness of $\omega$-limit sets then force convergence to a single point $(0, b)$. Condition (a) also makes the embedded network frozen at $b$ complex balanced, and $(\diamond)$ gives a coercivity estimate $D_\ell(z) \ge \delta A_\ell(z)$ for the vanishing species near $0$, showing that the total mass of $\Sigma$ is eventually increasing, which contradicts $z(t) \to 0$. Allowing several linkage classes is the novelty relative to the known single-linkage-class case.

## Sources

- C. Wiuf, "A Proof of the Global Attractor Conjecture in a Special Case", arXiv:2609.24553 (2026), Proposition 1.1, Theorem 1.2, Proposition 4.3, Corollaries 6.3 and 7.1, Theorem 7.2, <https://doi.org/10.48550/arXiv.2609.24553>.
