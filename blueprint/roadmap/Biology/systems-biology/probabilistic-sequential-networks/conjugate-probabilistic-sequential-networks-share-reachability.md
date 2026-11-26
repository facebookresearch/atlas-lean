# Conjugate probabilistic sequential networks share their reachability structure

**Sequential dynamical systems.** Let $\Gamma$ be a finite graph on vertices $\{1,\dots,n\}$ and $k_1,\dots,k_n$ finite sets of local states, with global state space $k^n=k_1\times\dots\times k_n$. A local function at vertex $a$ is a map $f_a:k^n\to k^n$ that changes only coordinate $a$, through a function of the coordinates adjacent to $a$ in $\Gamma$. Given one local function per vertex and an update schedule (a permutation $\alpha$ of the vertices), the global update is the composition of the local functions in the order prescribed by $\alpha$. This models a gene regulatory network in which genes are updated one at a time.

**Probabilistic sequential network (PSN).** A PSN $\mathcal D$ specifies, for each vertex $a$, a finite set $F_a$ of candidate local functions, and a finite set of update schedules. Each choice of one local function per vertex and one schedule yields an update function $f:k^n\to k^n$; the resulting finite set $S$ of update functions carries probabilities $c_f>0$ with $\sum_{f\in S}c_f=1$. The **state space** of $\mathcal D$ is the weighted digraph on $k^n$ with an arrow $u\to v$ of weight

$$p(u,v)=\sum_{f\in S:\ f(u)=v}c_f ,$$

so $T=(p(u,v))_{u,v}$ is the transition matrix of a Markov chain on $k^n$.

**Equivalence.** Two PSNs $\mathcal D_1,\mathcal D_2$ with update sets $S_1,S_2$ on state spaces $k^n$ and $k^m$ are **equivalent** if there are a bijection $h:k^n\to k^m$ (induced by a graph isomorphism and bijections of local state sets) and a bijection $\mu:S_1\to S_2$ such that

$$f=h^{-1}\circ\mu(f)\circ h\qquad\text{for all } f\in S_1,$$

while the probabilities $c_f$ and $d_{\mu(f)}$ may differ.

**Proposition.** If $\mathcal D_1$ and $\mathcal D_2$ are equivalent, with transition matrices $T_1$ and $T_2$, then for all $m\in\mathbb N$ and all states $u,v$,

$$(T_1^m)_{u,v}\neq0\iff(T_2^m)_{h(u),h(v)}\neq0 .$$

Hence equivalent PSNs have isomorphic reachability graphs: the same communicating classes, the same absorbing states (fixed points) and the same attractor structure up to relabelling by $h$, regardless of the probability weights. Equivalence is an equivalence relation, and PSNs with structure-preserving morphisms form a category containing deterministic sequential dynamical systems as a full subcategory.

## Expansion

An arrow $u\to v$ exists in $\mathcal D_1$ iff $f(u)=v$ for some $f\in S_1$, iff $\mu(f)(h(u))=h(f(u))=h(v)$, iff there is an arrow $h(u)\to h(v)$ in $\mathcal D_2$, since $\mu$ is onto $S_2$. Because all probabilities are strictly positive, $(T^m)_{u,v}>0$ exactly when there is a directed path of length $m$ from $u$ to $v$ in the state-space digraph, and $h$ maps such paths bijectively. Only the support of the transition matrices is preserved; stationary probabilities generally change with the weights.

## Sources

- Maria A. Avino-Diaz, "Introducing a Probabilistic Structure on Sequential Dynamical Systems, Simulation and Reduction of Probabilistic Sequential Networks", arXiv:0707.0026 (2007), Section 2; Section 3, Definitions 3.1 and 3.2; Section 5, Theorems 5.1–5.3; Section 7, Definition 7.1 and Proposition 7.2. <https://doi.org/10.48550/arXiv.0707.0026>
