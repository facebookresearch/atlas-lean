# Dynamic balance and ESS stability of replicator dynamics with migration

**Model.** A population game $(\mathcal Y, r)$ has actions $\mathcal A$, population states $y$ in the simplex and positive rewards $r_i(y)$. Individuals live in communities $\mathcal H$ with densities $\eta_h$ ($\sum_h\eta_h = 1$); $x_{ih}$ is the fraction of the population that is in community $h$ and plays $i$, and $y = x\mathbf 1$. Encounters between communities $h$ and $k$ have strength $W_{hk}$, with $W$ nonnegative, irreducible and with positive diagonal. Migration from $h$ to $k$ occurs at rate $\lambda_{hk}\phi_{hk}(x)$ with an environmental response $\phi \ge 0$. The co-evolution is

$$\dot\eta_h = \sum_k\lambda_{kh}\phi_{kh}(x)\eta_k - \eta_h\sum_k\lambda_{hk}\phi_{hk}(x),$$

$$\dot x_{ih} = \sum_k\lambda_{kh}\phi_{kh}(x)x_{ik} - x_{ih}\sum_k\lambda_{hk}\phi_{hk}(x) + \eta_h\sum_kx_{ik}W_{hk}r_i(y) - x_{ih}\sum_{j}\sum_kx_{jk}W_{hk}r_j(y),$$

a closed migration process coupled to a replicator equation on the community network.

**Theorem (dynamic balance).** If $x(t)\mathbf 1 \to y^*$, then $y^*$ is a restricted Nash equilibrium of the game, and in every community whose density stays bounded away from zero the local action frequencies converge to the global ones:

$$\lim_{t\to\infty}\frac{x_{ih}(t)}{\eta_h(t)} = y^*_i \quad\text{for all } i \in \mathcal A.$$

If moreover $\eta(t) \to \eta^*$, the system state converges to the rank-one matrix $y^*\eta^{*\top}$.

**Theorem (evolutionary stability).** If $W$ is symmetric and the game is a two-action matrix game, then an evolutionarily stable state $\hat y$ is locally asymptotically stable for the population state, and if $\hat y$ lies in the interior of the simplex, every interior trajectory converges to it.

## Proof sketch

Because migration is action-independent, it moves all actions of a community in proportion, so it cannot by itself change the global action frequencies; selection drives the population state, and mixing through the irreducible interaction matrix $W$ equalizes community compositions wherever communities remain occupied. At a limit point the replicator terms vanish only if every action in use earns the same reward, which is the restricted Nash condition. For symmetric $W$ and matrix games the classical replicator Lyapunov function $P(y) = \prod_i y_i^{\hat y_i}$ still increases along the population state, giving the ESS results. The framework covers rational community choice and density-dependent out-migration, as in ecological habitat selection.

## Sources

- Alain Govaert, Lorenzo Zino and Emma Tegling, "Population Games on Dynamic Community Networks", *IEEE Control Systems Letters* 6 (2022), 2695–2700, <https://doi.org/10.1109/lcsys.2022.3174916>. Preprint version: arXiv:2203.00371 (2022), Section 2 (model, Assumptions 1–2), Theorem 1, Corollary 1.1 and Theorem 2 (Section 3), <https://doi.org/10.48550/arXiv.2203.00371>.
