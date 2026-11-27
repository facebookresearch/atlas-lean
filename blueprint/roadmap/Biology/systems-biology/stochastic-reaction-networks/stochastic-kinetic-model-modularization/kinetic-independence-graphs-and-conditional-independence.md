# Kinetic independence graphs and conditional independence in stochastic kinetic models

**Stochastic kinetic models.** A stochastic kinetic model (SKM) $[N,S,\mathsf P]$ describes species $\mathcal V$ reacting through reactions $m\in\mathcal M$. It is the multivariate counting process $N(t)=(N_m(t))_{m\in\mathcal M}$ of reaction occurrences, with stoichiometric matrix $S$ (species counts are $X(t)=X(0)+SN(t)$) and mass-action-type conditional intensities $\lambda_m(t)$ that depend on the current counts of the reactants $R[m]$ of $m$. For $A\subseteq\mathcal V$ let $\Delta(A)=\{m:S^A_m\ne0\}$ be the reactions that change $A$. The subprocess $N^A$ is the counting process of $\Delta(A)$ with reactions grouped by identical effect on $A$; its intensity sums the $\lambda_m$ in each group, and its internal history $\mathcal F^A_t$ is equivalent to the history of the counts of $A$.

**Kinetic independence graph.** The KIG of the SKM is the directed (generally cyclic) graph on $\mathcal V$ with parent sets

$$\operatorname{pa}(k)=R[\Delta(k)]\setminus\{k\},$$

so $j\to k$ when $j$ is a reactant in a reaction that changes $k$. Let $G^\sim$ be its undirected version, and write $A\perp_{G^\sim}B\mid D$ when $D$ separates $A$ from $B$.

**Standard SKMs.** An SKM is *standard* if (i) every reaction changes at least one species ($S_m\ne0$ for all $m$); (ii) every species is changed by at least one reaction (each row $S_{k\bullet}\ne0$); (iii) a zeroth-order reaction ($R[m]=\emptyset$), if present, has exactly one product; (iv) for every $m$, if $|R[m]|=1$ then $|R^*[m]|=1$, and if $|R[m]|>1$ then $|R[m]\setminus R^*[m]|\le1$, where $R^*[m]=\{i\in R[m]:S_{im}\ne0\}$ are the reactants changed by $m$.

**Theorem.** Let $[A,B,D]$ partition $\mathcal V$.

*(1)* (Local independence) $\lambda^B(t)$ is $\mathcal F^{\operatorname{cl}(B)}_t$-measurable. If $A\perp_{G^\sim}B\mid D$, then $N^B$ is locally independent of $N^A$ given $N^{B\cup D}$, and symmetrically.

*(2)* (Global independence) Let the SKM be standard, and suppose the reactions $\Gamma=\Delta(A)\cap\Delta(B)$ are *identified by consumption of reactants*: each consumes, and never produces, its reactants, and no two of them consume reactants identically. Then $A\perp_{G^\sim}B\mid D$ implies

$$\mathcal F^A_t\perp\!\!\!\perp\mathcal F^B_t\ \big|\ \mathcal F^{D^*}_t\qquad\text{for all }t\ge0,$$

under both $\mathsf P_t$ and a reference measure $\tilde{\mathsf P}_t$. Here $N^{D^*}$ refines $N^D$ by recording separately the jumps of $D$ caused by reactions that also change $A$ only, $A$ and $B$, $B$ only, or $D$ alone. The likelihood ratio factorizes as $d\mathsf P_t/d\tilde{\mathsf P}_t=\psi_{AD^*,t}\,\psi_{BD^*,t}$, with each factor measurable with respect to its own side.

*(3)* (Sharpness) Under the same hypotheses (a standard SKM, the condition on $\Gamma$ and $A\perp_{G^\sim}B\mid D$), conditioning on $\mathcal F^D_t$ alone instead of $\mathcal F^{D^*}_t$ need not give conditional independence: in the standard SKM $A\rightleftharpoons D\to B$ (reactions $A\to D$, $D\to A$, $D\to B$, with KIG $A\leftrightarrow D\to B$) neither $\mathcal F^A_t\perp\!\!\!\perp\mathcal F^B_t\mid\mathcal F^D_t$ under $\mathsf P_t$ nor under $\tilde{\mathsf P}_t$ holds.

## Expansion

The KIG transfers the separation calculus of graphical models to jump processes. Local independence (in the sense of Didelez) says that the intensity of one group of species does not look at the history of another. The global statement follows from the Jacod likelihood formula for counting processes: under a unit-rate reference measure, the log-likelihood is a sum of reaction-wise terms, and separation lets each term be assigned to the $A$ or $B$ side given the $D^*$ jumps. The jumps of the separating set must be labelled by which side caused them, which is why $D^*$ and not $D$ is needed. This yields a rigorous notion of a *module* in a biochemical network, namely a set of species that is conditionally independent of the rest given the dynamics of its interface. Nested modularizations can be found by graph decomposition, as in the analysis of a red blood cell metabolism SKM.

## Sources

- Clive G. Bowsher, "Stochastic kinetic models: Dynamic independence, modularity and graphs", arXiv:1010.3916 (2010), Definitions 2.1–2.2 and 3.1 (SKMs, subprocesses, KIG), Propositions 2.2, 3.1–3.2, Definition 4.2 ($N^{D^*}$), Definition 4.3 (standard SKM), Condition 4.3, Theorems 4.4–4.5, Corollary 4.6 and Theorem 4.7, <https://doi.org/10.48550/arXiv.1010.3916>.
