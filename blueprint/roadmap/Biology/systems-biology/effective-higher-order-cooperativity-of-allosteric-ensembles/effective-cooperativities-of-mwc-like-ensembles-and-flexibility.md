# Effective cooperativities of MWC-like ensembles and the flexibility theorem

**Setting.** A target molecule has binding sites $1, \dots, n$ and conformations $c_1, \dots, c_N$. In conformation $c_k$, let $K_{c_k, i, S}$ be the association constant for ligand binding at site $i \notin S$ when exactly the sites in $S$ are bound, and $\omega_{c_k, i, S} = K_{c_k, i, S}/K_{c_k, i, \emptyset}$ the intrinsic higher-order cooperativity (HOC) of order $\#S$. The system is at thermodynamic equilibrium; let $\Pr_{c_k}$ be the equilibrium probability of conformation $c_k$ among empty (unbound) conformations and $\langle X(c_k) \rangle = \sum_{k} X(c_k)\Pr_{c_k}$. Let $\mu_S(c_k)$ be the product of equilibrium labels (association constants) along any binding path from the empty state to binding pattern $S$ within conformation $c_k$.

**Effective parameters.** Coarse-graining over conformations at equilibrium gives a single-conformation binding graph with effective association constants and effective HOCs

$$K^{\phi}_{i, S} = \frac{\langle K_{c_k, i, S}\, \mu_S(c_k) \rangle}{\langle \mu_S(c_k) \rangle}, \qquad \omega^{\phi}_{i, S} = \frac{\langle K_{c_k, i, S}\, \mu_S(c_k) \rangle}{\langle K_{c_k, i, \emptyset}\rangle\, \langle \mu_S(c_k) \rangle}.$$

These do not depend on ligand concentration, satisfy $\omega^\phi_{i,\emptyset} = 1$, and reduce to the intrinsic HOC when $N = 1$.

**Proposition (MWC-like ensembles).** Suppose there is no intrinsic cooperativity ($K_{c_k, i, S} = K_{c_k, i, \emptyset}$) and the sites are identical in each conformation ($K_{c_k, i, \emptyset} = K_{c_k}$), with any number $N$ of conformations. Then $\omega^\phi_{i,S}$ depends only on $s = \#S$ and

$$\omega^{\phi}_{s} = \frac{\langle K_{c_k}^{\,s+1} \rangle}{\langle K_{c_k} \rangle \langle K_{c_k}^{\,s} \rangle}, \qquad s = 0, 1, \dots, n-1 .$$

In particular the effective pairwise cooperativity is $\omega^\phi_1 = \langle K_{c_k}^2\rangle / \langle K_{c_k}\rangle^2$, and if $K_{c_k}$ is not constant over conformations,

$$1 < \omega^{\phi}_1 < \omega^{\phi}_2 < \cdots < \omega^{\phi}_{n-1}.$$

MWC-like ensembles thus produce only positive effective cooperativity, increasing with order; negative effective HOCs require non-identical sites.

**Theorem (flexibility).** For any $n$, any positive targets $\beta_i$ for the effective bare constants $K^\phi_{i,\emptyset}$ and any positive targets for the independent effective HOCs $\omega^\phi_{i,S}$ ($i < \min S$), and any accuracy, there is an allosteric ensemble with $2^n$ conformations, no intrinsic cooperativity in any conformation, and suitable conformational probabilities and bare association constants whose effective parameters approximate all targets to that accuracy. Conversely, a dimension count over the free parameters of an ensemble with $N$ conformations and no intrinsic cooperativity ($n$ bare constants per conformation and $N-1$ conformational equilibrium labels) shows that the effective HOCs cannot take arbitrary values when $n(N - 1) < 2^n - 1$.

## Expansion

With independent identical sites, $\mu_S(c_k) = K_{c_k}^{\#S}$, and substituting into the general formula gives the moment ratio. Writing $M_s = \langle K^s\rangle$ for moments of a non-degenerate positive random variable, log-convexity of $s \mapsto M_s$ (Hölder or Cauchy–Schwarz: $M_s^2 < M_{s-1}M_{s+1}$) means $M_{s+1}/M_s$ is strictly increasing in $s$, so $\omega^\phi_s = (M_{s+1}/M_s)/M_1$ is strictly increasing with $\omega^\phi_0 = 1$. The flexibility construction indexes conformations by subsets $T \subseteq \{1, \dots, n\}$, gives conformation $c_T$ high affinity (by a factor $\varepsilon^{-1}$) at the sites in $T$, and assigns the empty-conformation weights $\lambda_T$ freely; as $\varepsilon, \delta \to 0$ the effective HOCs approach prescribed values, showing that conformational ensembles alone, without pairwise interactions between sites, have unlimited capacity to integrate binding information.

## Sources

- J. W. Biddle, R. Martinez-Corral, F. Wong, J. Gunawardena, "Allosteric conformational ensembles have unlimited capacity for integrating information", eLife 10 (2021) e65498, Results (HOC definition; coarse-grained effective parameters, Eq. 18; MWC-like ensembles, Eqs. 19–20; flexibility theorem, Eqs. 21–27, Figures 6–8) and Materials and methods (Lemmas 1–2, Theorem 1), <https://doi.org/10.7554/eLife.65498> (PMC8189718).
- J. Monod, J. Wyman, J.-P. Changeux, "On the nature of allosteric transitions: a plausible model", Journal of Molecular Biology 12 (1965) 88–118, <https://doi.org/10.1016/S0022-2836(65)80285-6>.
