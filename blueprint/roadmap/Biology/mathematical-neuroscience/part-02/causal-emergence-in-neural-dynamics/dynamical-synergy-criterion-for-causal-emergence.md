# Dynamical synergy criterion for causal emergence

**Setting.** A system of $n$ parts (for example $n$ recording channels) is observed at times $t < t'$ as $X_t = (X_t^1, \dots, X_t^n)$, with joint dynamics given by $p(x_{t'} \mid x_t)$. A process $V_t$ is *supervenient* on $X_t$ if $V_t - X_t - X_{t''}$ is a Markov chain for every $t'' \ne t$ (given the full micro-state, the feature adds no information about other times; deterministic features $V_t = F(X_t)$ and noisy ones $F(X_t) + \nu_t$ qualify).

Fix a partial information decomposition (PID) $I(X; Y) = \sum_{\alpha \in \mathcal A} I_\partial^{\alpha}(X; Y)$ over the antichain lattice $\mathcal A$ of collections of source subsets, satisfying the basic PID axioms. Define:

- *$k$th-order synergy* $\mathrm{Syn}^{(k)}(X; Y) = \sum_{\alpha \in \mathcal S^{(k)}} I_\partial^\alpha(X; Y)$, where $\mathcal S^{(k)}$ contains the collections all of whose members have more than $k$ sources: information about $Y$ in the whole that no set of $k$ or fewer parts carries on its own;
- *$k$th-order unique information* $\mathrm{Un}^{(k)}(V; Y \mid X)$: information $V$ carries about $Y$ that no group of $k$ or fewer parts of $X$ carries.

**Definition.** A supervenient $V_t$ exhibits *causal emergence of order $k$* if $\mathrm{Un}^{(k)}(V_t; X_{t'} \mid X_t) > 0$.

**Theorem.** The system has a causally emergent feature of order $k$ if and only if

$$\mathrm{Syn}^{(k)}(X_t; X_{t'}) > 0,$$

and every supervenient feature satisfies $\mathrm{Un}^{(k)}(V_t; X_{t'} \mid X_t) \le \mathrm{Syn}^{(k)}(X_t; X_{t'})$, so dynamical synergy is the system's *emergence capacity*.

**Taxonomy.** Using the integrated information decomposition (which splits each PID atom by source and target lattices, $I_\partial^\alpha = \sum_\beta I_\partial^{\alpha \to \beta}$), the capacity splits as

$$\mathrm{Syn}^{(k)}(X_t; X_{t'}) = \mathcal G^{(k)}(X_t; X_{t'}) + \mathcal D^{(k)}(X_t; X_{t'}),$$

with $\mathcal D^{(k)}$ summing atoms from $\mathcal S^{(k)}$ to targets outside $\mathcal S^{(k)}$ and $\mathcal G^{(k)}$ summing atoms from $\mathcal S^{(k)}$ to $\mathcal S^{(k)}$. The system admits features exerting *downward causation* of order $k$ (unique information about some $k$-tuple of future parts) iff $\mathcal D^{(k)} > 0$, and features showing *causal decoupling* (unique information about their own future beyond all parts at both times) iff $\mathcal G^{(k)} > 0$; it is perfectly decoupled if $\mathcal G^{(k)} > 0$ and $\mathcal D^{(k)} = 0$.

A feature that is causally emergent of order $1$ requires $n \ge 2$ and cannot be a deterministic function of a single part.

## Expansion

Both directions rest on supervenience and the PID axioms. Since $V_t$ is a (possibly noisy) function of $X_t$, any information $V_t$ holds about $X_{t'}$ is contained in $I(X_t; X_{t'})$; information that is unique to $V_t$ relative to every $k$-group of parts must sit in atoms of $I(X_t; X_{t'})$ not attributable to any such group, that is in the $k$th-order synergy. This gives the bound, hence "only if". Conversely, if $\mathrm{Syn}^{(k)} > 0$, a feature that encodes exactly the synergistic component of $X_t$ about $X_{t'}$ (a synergistic channel) is supervenient and has positive unique information. The taxonomy refines the same argument by tracking whether the synergistic source information lands on targets carried by small groups of future parts ($\mathcal D$) or only on future collective properties ($\mathcal G$).

## Sources

- F. E. Rosas, P. A. M. Mediano, H. J. Jensen, A. K. Seth, A. B. Barrett, R. L. Carhart-Harris, D. Bor, "Reconciling emergences: An information-theoretic approach to identify causal emergence in multivariate data", *PLoS Computational Biology* 16(12) (2020) e1008289. Section "A formal theory of causal emergence" (Definition 1; PID, Eq. (1); Definition 2, Eq. (2); Lemma 1; Theorem 1, Eq. (3); Corollary 1) and "A taxonomy of emergence" (Eqs. (4)–(7); Definitions 3–4; Theorems 2–3). <https://doi.org/10.1371/journal.pcbi.1008289>. PMCID: PMC7833221.
