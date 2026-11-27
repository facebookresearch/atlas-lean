# Functional pigeonhole principle formulas are hard for polynomial calculus

The graph functional pigeonhole principle on a bipartite boundary expander with bounded left degree requires linear polynomial calculus degree, hence exponential size; consequently the standard CNF encoding of the functional pigeonhole principle with $n+1$ pigeons and $n$ holes needs size $\exp(\Omega(n))$ in polynomial calculus resolution.

Let $G = (U \,\dot\cup\, V, E)$ be bipartite, with pigeons $U$ and holes $V$, and variables $x_{u,v}$ for $(u,v) \in E$. The formula $\mathrm{FPHP}_G$ consists of the pigeon axioms $\bigvee_{v \in N(u)} x_{u,v}$ for $u \in U$, the hole axioms $\neg x_{u,v} \vee \neg x_{u',v}$ for $v \in V$ and distinct $u, u' \in N(v)$, and the functionality axioms $\neg x_{u,v} \vee \neg x_{u,v'}$ for $u \in U$ and distinct $v, v' \in N(u)$. $G$ is an $(s, \delta)$-boundary expander if every $U' \subseteq U$ with $|U'| \le s$ has at least $\delta |U'|$ vertices of $V$ with exactly one neighbour in $U'$.

**Theorem.** If $G$ is a bipartite $(s, \delta)$-boundary expander with left degree at most $d$, then refuting $\mathrm{FPHP}_G$ in polynomial calculus requires degree strictly greater than $\delta s/(2d)$. If $G$ is a bipartite $(\gamma n, \delta)$-boundary expander with constant left degree and constants $\gamma, \delta > 0$, then every polynomial calculus (PC or PCR) refutation of $\mathrm{FPHP}_G$ has size $\exp(\Omega(n))$.

**Corollary.** Every polynomial calculus or polynomial calculus resolution refutation of the standard CNF encoding of $\mathrm{FPHP}^{n+1}_n$ has size $\exp(\Omega(n))$.

## Expansion

Put the hole and functionality axioms into $\mathcal{E}$, the pigeon axioms as singletons into $\mathcal{U}$, and for each hole $v$ let $V_v = \{x_{u',v'} : u' \in N(v), v' \in N(u')\}$. Setting all of $V_v$ false respects $\mathcal{E}$, and the assignment putting $x_{u,v}$ true and the rest of $V_v$ false $\mathcal{E}$-respectfully satisfies the pigeon axiom of $u$, so the clustered graph is isomorphic to $G$ with all neighbours respectful and is an $(s, \delta, 0, \mathcal{E})$-expander of overlap at most $d$; the generalized degree theorem applies, and the size-degree relation gives the size bound. The corollary follows by restricting $\mathrm{FPHP}^{n+1}_n$ to a good expander of left degree $3$, since restrictions do not increase refutation size. This answered an open question of Razborov; Onto-FPHP is easy for polynomial calculus while FPHP and Onto-PHP are hard.

## Depends on

None.

## Proof depends on

- [Generalized polynomial calculus degree lower bound via respectful boundary expansion](respectful-boundary-expansion-pc-degree-lower-bound.md)
- [Size-degree relation for polynomial calculus](polynomial-calculus-size-degree-relation.md)

## Sources

- Mladen Mikša, Jakob Nordström, "A generalized method for proving polynomial calculus degree lower bounds", *30th Computational Complexity Conference (CCC 2015)*, LIPIcs 33, 2015, https://doi.org/10.4230/LIPIcs.CCC.2015.467; numbering of the full version, ECCC report TR15-078 (Definition 4.1, Theorems 4.9 and 4.10).
