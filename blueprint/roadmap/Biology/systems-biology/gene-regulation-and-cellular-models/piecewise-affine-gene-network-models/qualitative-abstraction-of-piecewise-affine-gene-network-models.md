# Qualitative abstraction of piecewise-affine gene network models

**Model.** A piecewise-affine differential equation (PADE) model of a genetic regulatory network with concentrations $x \in \Omega \subset \mathbb{R}_{\ge 0}^n$ has the form

$$\dot x_i = \sum_{l \in L_i} \kappa_{il}\, b_{il}(x) - \gamma_i x_i, \qquad i = 1, \dots, n,$$

with synthesis constants $\kappa_{il} > 0$, degradation constants $\gamma_i > 0$, and regulation functions $b_{il}(x) \in \{0, 1\}$ that are Boolean combinations of step functions $s^+(x_j, \theta_j) = 1$ if $x_j > \theta_j$ and $0$ if $x_j < \theta_j$, with $s^- = 1 - s^+$. At thresholds the step functions are replaced by the interval extension $S^\pm(\theta_j, \theta_j) = [0, 1]$, turning the system into a differential inclusion (Filippov solutions).

**Partition.** Let $\Theta_i = \{\theta_{ij}\}$ be the thresholds of $x_i$ and $\Lambda_i = \{\sum_{l \in B} \kappa_{il} / \gamma_i : B \subseteq L_i\}$ its **focal values**. The hyperplanes $x_i = c$, $c \in \Theta_i \cup \Lambda_i$, define a rectangular partition $\mathcal{D}$ of $\Omega$ into domains (open boxes and their lower-dimensional faces). In each domain $D$ the interval-valued regulation functions are constant, $B_{il}(x) = B_{il}(D)$, so every component of the vector field has a constant sign pattern on $D$.

**State transition graph.** The qualitative dynamics is the graph on $\mathcal{D}$ with an edge $D \to D'$ when some solution starting in $D$ reaches $D'$ without leaving $D \cup D'$. With $F_i(D, D') = \sum_{l} \kappa_{il} B_{il}(D) - \gamma_i D'_i$ evaluated in interval arithmetic, a **dimension-increasing transition** $D \to D'$ with $D \subseteq \partial D'$ exists iff (Proposition 1)

1. for every $i$ with $D_i = D'_i$ equal to a value in $\Theta_i \cup \Lambda_i$, $0 \in F_i(D', D)$; and
2. for every $i$ with $D_i \ne D'_i$, some $\alpha > 0$ satisfies $\alpha \in F_i(D', D)\,(D'_i - D_i)$.

**Parameter invariance.** The signs of $F_i$, hence all transitions and the whole state transition graph, are invariant over each region of parameter space defined by a total order on $\Theta_i \cup \Lambda_i$ for every $i$. Qualitative behaviour therefore depends only on finitely many **parametrizations** (orderings), not on exact parameter values.

## Expansion

Inside an open box every regulator is strictly above or below each threshold, so the dynamics is linear with a single attracting point (the focal point $\sum_l \kappa_{il} b_{il} / \gamma_i$ in each coordinate), and each $x_i$ moves monotonically toward it; this is why focal values must be added to the partition to freeze derivative signs. Finitely many orderings yield finitely many transition graphs, and a temporal-logic property (e.g. a time-series observation encoded in CTL) holds for all models of a parametrization iff it holds on that graph. Encoding the orderings symbolically and model checking all of them at once avoids enumerating parametrizations, which is how the method tests consistency of a synthetic five-gene network with expression data and searches for re-engineered parametrizations.

## Sources

- G. Batt, M. Page, I. Cantone, G. Goessler, P. Monteiro, H. de Jong, "Efficient parameter search for qualitative models of regulatory networks using symbolic model checking", Bioinformatics (2010), Sections 2.3 and 3.1, Equations (1)–(3), Proposition 1, <https://doi.org/10.1093/bioinformatics/btq387> (PMC2935427).
