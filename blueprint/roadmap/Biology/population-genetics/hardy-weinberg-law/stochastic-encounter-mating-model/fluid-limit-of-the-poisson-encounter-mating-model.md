# Fluid limit of the Poisson encounter-mating model

Consider the stochastic encounter-mating model with Poisson firing times, so that its law is determined by the matrix $\Pi = (\pi_{ij})$, $\pi_{ij} = p_{ij}(\alpha_i + \beta_j) > 0$ (see [Fine balance characterization of panmixia in the stochastic encounter-mating model](fine-balance-characterization-of-panmixia-in-encounter-mating.md)). Take a sequence of populations of size $n$ with $x^{(n)}_i/n \to x_i$ and $y^{(n)}_j/n \to y_j$, $\sum_i x_i = \sum_j y_j = 1$, and let $Q^{(n)}(t)$ be the pair-type process and $T_n$ its terminal time. Define on $k\times k$ matrices $M$ with $M_{\mathrm{tot}} = \sum_{ij}M_{ij} \ne 1$

$$F_{ij}(M) = \frac{\pi_{ij}\,(x_i - M_{i\cdot})(y_j - M_{\cdot j})}{1 - M_{\mathrm{tot}}},$$

and $F_{ij}(M) = 0$ if $M_{\mathrm{tot}} = 1$.

**Theorem.**

1. (Fluid limit.) There is a deterministic $Q(t)$ with $Q(t) = \int_0^t F(Q(s))\,ds$ such that for every $T < \infty$, almost surely $\sup_{0\le t\le T}|n^{-1}Q^{(n)}(t) - Q(t)| \to 0$; moreover $n^{-1}Q^{(n)}(T_n) \to Q(\infty)$ almost surely, so the limiting mating pattern is $Q(\infty)$.
2. (Replicator form.) Let $X_i = x_i - Q_{i\cdot}$, $Y_j = y_j - Q_{\cdot j}$, $Z = 1 - Q_{\mathrm{tot}}$ (single densities), $A_i = X_i/Z$, $B_j = Y_j/Z$, and $\hat\Pi = \begin{pmatrix}0 & \Pi\\ \Pi^{T} & 0\end{pmatrix}$. Then $U = (X, Y)$ solves the Lotka–Volterra system $\dot U_i = -Z^{-1}U_i(\hat\Pi U)_i$, and $C = \tfrac12(A, B)$ solves the replicator system

$$\dot C_i = -2C_i\big[(\hat\Pi C)_i - C^{T}\hat\Pi C\big], \qquad i \in \{1,\dots,2k\}.$$

3. (Fine balance.) If $\pi_{ij} = \bar\alpha_i + \bar\beta_j$ with $\bar\alpha_i, \bar\beta_j \ge 0$, then

$$A_i(t) = \frac{x_ie^{-\bar\alpha_i t}}{\sum_{i'}x_{i'}e^{-\bar\alpha_{i'}t}}, \qquad B_j(t) = \frac{y_je^{-\bar\beta_j t}}{\sum_{j'}y_{j'}e^{-\bar\beta_{j'}t}}, \qquad Q_{ij}(t) = x_iy_j\big(1 - e^{-\pi_{ij}t}\big),$$

so $Q_{ij}(\infty) = x_iy_j$ (panmixia in the limit).

4. (Symmetric $2\times 2$ case.) If $k = 2$, $\pi_{12} = \pi_{21}$ and $x_1 = y_1 \in (0,1)$, then $Q_{12}(\infty) < x_1(1-x_1)$ (homogamy), $= x_1(1-x_1)$ (panmixia) or $> x_1(1-x_1)$ (heterogamy) according as $\pi_{11} + \pi_{22}$ is $>$, $=$ or $<$ $2\pi_{12}$.

## Depends on

- [Fine balance characterization of panmixia in the stochastic encounter-mating model](fine-balance-characterization-of-panmixia-in-encounter-mating.md)
- [Orbital equivalence, replicator to Lotka–Volterra](../../../population-dynamics/replicator-and-lotka-volterra-equivalence/replicator-orbit-equiv-lotka-volterra.md)

## Expansion

The rescaled jump rates are $nF^{(n)}_{ij}(n^{-1}Q^{(n)})$, so $Q^{(n)}_{ij}(t) = J_{ij}\big(n\int_0^tF^{(n)}_{ij}(n^{-1}Q^{(n)}(s))\,ds\big)$ for independent unit Poisson processes $J_{ij}$, and Kurtz-type arguments give the fluid limit. The vector field is not globally Lipschitz near $M_{\mathrm{tot}} = 1$; the proof shows that $1 - n^{-1}Q^{(n)}_{\mathrm{tot}}(T) \ge e^{-cT}$ eventually for any $c > \max\pi_{ij}$, which keeps the process away from the singularity. Differentiating the single densities gives $\dot X_i = -Z^{-1}X_i(\Pi Y)_i$, a Lotka–Volterra system, and normalizing by $Z$ turns it into a replicator system. Under fine balance the payoff $(\Pi B)_i = \bar\alpha_i + \bar\beta\cdot B$ splits, so the replicator equation for $A$ decouples into exponential tilts.

## Sources

- Onur Gün, Atilla Yilmaz, "Fluid limit for the Poisson encounter-mating model", *Advances in Applied Probability* 49 (2017), 1201–1229, <https://doi.org/10.1017/apr.2017.39>; preprint arXiv:1411.7220, <https://doi.org/10.48550/arXiv.1411.7220>. Numbering of the latest arXiv version, which carries the published title: Theorem 2.1, Lemma 2.3, Theorem 2.5, Theorem 3.1, Theorem 3.3, Theorem 4.1.
