# Polymorphic evolution sequence with phenotypic plasticity

**Model.** Individuals carry a genotype $g\in\mathcal G$ and a phenotype $p\in\mathcal P$ (finite sets, $\mathcal X=\mathcal G\times\mathcal P$). In a population of carrying-capacity scale $K$, an individual of type $(g,p)$ gives birth at rate $b(p)$, dies naturally at rate $d(p)$ and from competition at rate $\sum c(p,\tilde p)\,n_{(\tilde g,\tilde p)}/K$; it switches phenotype $p\to\tilde p$ within its genotype at the *natural* rate $s^g_{\rm nat}(p,\tilde p)$ plus an *induced* rate $\sum_{\hat x}s^g_{\rm ind}(p,\tilde p)(\hat p)\,n_{\hat x}/K$ depending on the environment; a newborn is a mutant with probability $m(g)u_K$, its type drawn from a kernel $M$. Write $[p]_g$ for the communicating class of $p$ under switching for genotype $g$, and $\nu^K_t$ for the rescaled population measure on $\mathcal X$.

**Large-population limit.** With $u_K\equiv1$ and $\nu^K_0\to\nu_0$ a.s., $\nu^K\to\xi$ uniformly on $[0,T]$ in total variation, where $\xi$ solves a deterministic system; without mutation this is the *Lotka–Volterra system with plasticity* $LVS$ on the types $\mathcal X_{(\mathbf g,\mathbf p)}$ reachable by switching from residents $(g_1,p_1),\dots,(g_d,p_d)$:

$$\dot{\mathfrak n}_{(g,p)}=\mathfrak n_{(g,p)}\Bigl(b(p)-d(p)-\sum_{\tilde x}c(p,\tilde p)\mathfrak n_{\tilde x}-\sum_{\tilde p\in[p]_g}\sigma^g(p,\tilde p)\Bigr)+\sum_{\tilde p\in[p]_g}\mathfrak n_{(g,\tilde p)}\,\sigma^g(\tilde p,p),\qquad \sigma^g(p,\tilde p)=s^g_{\rm nat}(p,\tilde p)+\sum_{\hat x}s^g_{\rm ind}(p,\tilde p)(\hat p)\,\mathfrak n_{\hat x}.$$

Residents *coexist* if $LVS$ has a unique positive equilibrium $\bar{\mathfrak n}(\mathbf g,\mathbf p)$ with all Jacobian eigenvalues of negative real part.

**Theorem (PESP).** Assume switching rates are either identically zero or positive in every environment, all switching classes are recurrent, and every invading mutant drives $LVS$ from near $(\bar{\mathfrak n},0)$ to a unique new stable equilibrium $\mathfrak n^*$. Start from coexisting residents with $\nu^K_0\to\sum_x\bar{\mathfrak n}_x\delta_x$ and let

$$e^{-VK}\ll u_K\ll\frac{1}{K\ln K}\quad\text{for all }V>0 .$$

Then $(\nu^K_{t/(Ku_K)})_{t\ge0}$ converges in finite-dimensional distributions to a pure-jump process $\Lambda$ on equilibria: from $\sum_x\bar{\mathfrak n}_x(\mathbf g,\mathbf p)\delta_x$ it jumps to $\sum_x\mathfrak n^*_x\delta_x$, the equilibrium of residents plus mutant $(\tilde g,\tilde p)$, at rate

$$m(\hat g)\,b(\hat p)\,\bar{\mathfrak n}_{(\hat g,\hat p)}\bigl(1-q_{(\mathbf g,\mathbf p)}(\tilde g,\tilde p)\bigr)M\bigl((\hat g,\hat p),(\tilde g,\tilde p)\bigr),$$

where $1-q$ is the survival probability of the multitype branching process (types = phenotypes in $[\tilde p]_{\tilde g}$) approximating the mutant clone in the resident environment, i.e. $q$ is the extinction vector solving $u(\mathbf y)=0$ for the associated offspring generating map. Convergence cannot hold in the Skorokhod topology.

## Expansion

Rare mutations separate time scales: between mutations ($\sim1/(Ku_K)$) the resident population sits near $\bar{\mathfrak n}$ for times $e^{VK}$ by large deviations. A mutant clone evolves in three steps: (i) while small it is a multitype linear birth–death–switching process whose growth is governed by the principal eigenvalue of its mean matrix, and it survives with probability $1-q$; (ii) once of order $K$, the full $LVS$ carries the population to $\mathfrak n^*$ in time $O(1)$; (iii) types that lose decline as a subcritical branching process and die out in time $O(\ln K)$. The upper bound $u_K\ll1/(K\ln K)$ ensures no new mutant arrives during steps (i)–(iii). Plasticity replaces the scalar invasion fitness of the classical polymorphic evolution sequence by the branching-process survival probability, so a genotype can invade through a phenotype that is not itself fit, using switching.

## Sources

- Martina Baar, Anton Bovier, "The polymorphic evolution sequence for populations with phenotypic plasticity", Electronic Journal of Probability 23 (2018), 1–27, <https://doi.org/10.1214/18-ejp194>. Published version of arXiv:1708.01528, cited next; locators there refer to the arXiv version.
- M. Baar, A. Bovier, "The Polymorphic Evolution Sequence for Populations with Phenotypic Plasticity", arXiv:1708.01528 (2017), Section 2 (model and Theorem 2.1), Section 3 (Definitions 3.1–3.2, Assumptions, Theorem 3.3, Theorem 3.4, Theorem 3.6 and Lemma 3.7). <https://doi.org/10.48550/arXiv.1708.01528>
