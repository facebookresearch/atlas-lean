# Threshold and final size of SIR epidemics on random intersection graphs

**Graph.** Fix $\alpha>0$ and non-negative weight variables $A$ (individuals) and $B$ (groups) with $\mu=\mathbb E[A]=\alpha\,\mathbb E[B]\in(0,\infty)$. Take $n$ individuals with i.i.d. weights $A_i\sim A$ and $\lfloor\alpha n\rfloor$ groups with i.i.d. weights $B_j\sim B$; individual $i$ and group $j$ share a $\mathrm{Poisson}(A_iB_j/(\mu n))$ number of bipartite edges, independently. The **random intersection graph** $G^{(n)}$ joins two individuals iff they share a group. Asymptotically an individual belongs to $X\sim\mathcal{MP}(A)$ cliques (mixed Poisson) and a clique has $\mathcal{MP}(B)$ members. Write $\tilde Z$ for the size-biased version of $Z$, $\check X\sim\mathcal{MP}(\tilde A)$, $\check Y\sim\mathcal{MP}(\tilde B)$.

**Epidemic.** One uniformly chosen initial infective; each infective contacts each neighbor at rate $1$ during an i.i.d. infectious period $\mathcal I$ with $\mathbb P(\mathcal I=0)=0$ (infinite periods allowed). Let $T(m)$ be the number infected in a single-clique (local) SIR epidemic among $m$ susceptibles started by one infective, and $S(m)$ the size of a local susceptibility set (the members of the clique from whom infection could reach a given individual).

**Threshold parameter.**

$$R_\ast=\mathbb E_{\check Y}\bigl[\mathbb E[T(\check Y)\mid\check Y]\bigr]\;\mathbb E[\tilde A]=\mathbb E_{\check Y}\bigl[\mathbb E[S(\check Y)\mid\check Y]\bigr]\;\mathbb E[\tilde A],$$

the mean number of individuals infected through the local epidemics triggered by a typical non-initial infective in its other cliques (the equality uses $\mathbb E[T(m)]=\mathbb E[S(m)]$ by symmetry).

The **forward branching process** $\mathcal Z^f$ has the infectious period as type: the ancestor's offspring are the members infected in local epidemics in its $X$ cliques of sizes $\check Y_i+1$, later individuals use $\check X$ new cliques. The **backward branching process** $\mathcal Z^b$ is single-type, with offspring $\sum_{i\le X}S(\check Y_i)$ for the ancestor and $\sum_{i\le\check X}S(\check Y_i)$ afterwards. Let $\rho$ and $\rho^b$ be their survival probabilities, and $\mathcal R^{(n)}$ the set of ultimately recovered individuals.

**Theorem.**

1. $\rho>0$ if and only if $R_\ast>1$; the type-dependent survival function of $\mathcal Z^f$ is the unique non-zero solution (when one exists) of its fixed-point equation.
2. For every $k\in\mathbb N$, $\lim_{n\to\infty}\mathbb P(|\mathcal R^{(n)}|=k)=\mathbb P(|\mathcal Z^f|=k)$.
3. If $R_\ast>1$, then for every $0<\varepsilon<\rho^b$, $\lim_{n\to\infty}\mathbb P\bigl(\bigl|\,|\mathcal R^{(n)}|/n-\rho^b\bigr|<\varepsilon\bigr)=\rho$.
4. $n^{-1}|\mathcal R^{(n)}|\Rightarrow T_F$, where $\mathbb P(T_F=\rho^b)=\rho=1-\mathbb P(T_F=0)$.

When $R_\ast>1$, $\rho^b=1-f_{C^b}(\xi)$ where $\xi\in[0,1)$ solves $f_{\tilde C^b}(s)=s$, with $f_{C^b}(s)=\phi_A\bigl(1-\mathbb E_{\check Y}[f_{S(\check Y)\mid\check Y}(s)]\bigr)$ and $f_{\tilde C^b}(s)=\phi_{\tilde A}\bigl(1-\mathbb E_{\check Y}[f_{S(\check Y)\mid\check Y}(s)]\bigr)$, $\phi_A(\theta)=\mathbb E e^{-\theta A}$. If $\mathcal I$ is constant, $T(m)\overset d=S(m)$ and $\rho=\rho^b$; otherwise the probability of a major outbreak and its size generally differ.

## Expansion

Explore the graph from the initial infective: as long as the cliques used are disjoint (true with probability tending to one until the exploration reaches size $o(\sqrt n)$), each infective spawns independent local epidemics in its new cliques, giving the coupling with $\mathcal Z^f$; the size biasing reflects that a newly reached individual or clique is reached with probability proportional to its weight. Individuals in a litter share the infective's infectious period, so for non-constant $\mathcal I$ the process is multitype with type space $(0,\infty]$, and survival is analyzed through a monotone functional $\tilde\Phi$ on test functions. For the final size, the susceptibility set of a uniformly chosen individual is explored backwards for $\lceil\log\log n\rceil$ generations and coupled to $\mathcal Z^b$; if it survives it has polylogarithmic size, and a major outbreak, which infects $\Theta(n)$ individuals, then hits it with probability tending to one. Asymptotic independence of the susceptibility sets of two individuals yields the law of large numbers for $|\mathcal R^{(n)}|/n$.

## Sources

- Frank Ball, David Sirl, Pieter Trapman, "Epidemics on random intersection graphs", arXiv (2010); Annals of Applied Probability 24 (2014). Section 2 (graph and epidemic model), Section 3 (definitions of $R_\ast$, $\mathcal Z^f$, $\mathcal Z^b$; Theorems 3.3, 3.4, 3.5), Section 4 (Lemma 4.1, Theorem 4.2). <https://doi.org/10.48550/arXiv.1011.4242>. Published version: The Annals of Applied Probability 24(3) (2014), 1081–1128, <https://doi.org/10.1214/13-aap942>; locators above refer to the arXiv version.
