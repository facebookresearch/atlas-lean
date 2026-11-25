# Equilibrium classes order the prices of anarchy

In a cost game with finitely many players, finite nonempty strategy sets and $\mathrm{OPT} > 0$, the prices of anarchy of mixed Nash (for the payoffs
$u_i = -c_i$), correlated and coarse correlated equilibria, all three classes being nonempty, satisfy
$\mathrm{PoA}_{\mathrm{mixed}} \le \mathrm{PoA}_{\mathrm{CE}} \le \mathrm{PoA}_{\mathrm{CCE}}$. If the game has a pure Nash equilibrium, then also
$\mathrm{PoA}_{\mathrm{pure}} \le \mathrm{PoA}_{\mathrm{mixed}}$. If the game is $(\lambda, \mu)$-smooth with $\mu < 1$, then $\mathrm{PoA}_{\mathrm{CCE}} \le \lambda / (1 - \mu)$, so each of these
prices of anarchy is at most $\lambda / (1 - \mu)$.

## Proof

A pure Nash equilibrium, as a point mass, is a mixed Nash equilibrium; a mixed Nash equilibrium, as the product distribution of its strategies, is a
correlated equilibrium; and every correlated equilibrium is a coarse correlated equilibrium. Each class is contained in the next with the same expected
social cost; the mixed class is nonempty by Nash's theorem, so all later classes are nonempty, and a supremum over a larger set is at least as
large. The extension theorem with $\varepsilon = 0$ and $t$ an optimal profile bounds the expected social cost of every coarse correlated equilibrium by
$\lambda / (1 - \mu)$ times $\mathrm{OPT}$.

## Depends on

- [Price of anarchy and price of stability](remaining-clauses-of-social-cost-price-of-anarchy-and-stabil.md)
- [Smooth game](is-smooth.md)

## Proof depends on

- [Nash's theorem](../nash-s-theorem/exists-is-mixed-nash.md)
- [Mixed Nash equilibria are correlated equilibria](../correlated-equilibria/is-correlated-eq-product-dist-of-is-mixe.md)
- [Correlated equilibria are coarse correlated equilibria](../correlated-equilibria/is-coarse-correlated-eq.md)
- [Extension theorem for coarse correlated equilibria](expected-social-cost-le.md)

## Sources

- T. Roughgarden, *Intrinsic robustness of the price of anarchy*, Journal of the ACM 62(5) (2015); arXiv:1203.1638, Section 1 (the nested equilibrium concepts: pure Nash, mixed Nash, correlated and coarse correlated equilibria). Background reference. <https://arxiv.org/abs/1203.1638>
