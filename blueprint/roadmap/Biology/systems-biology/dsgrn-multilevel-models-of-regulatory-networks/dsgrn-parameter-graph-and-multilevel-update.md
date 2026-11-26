# DSGRN parameter graph and multilevel update of a regulatory network

**Regulatory network.** $RN=(V,E,\delta)$ is a directed graph on $V=\{1,\dots,N\}$ with edge signs $\delta:E\to\{\pm1\}$ (activating or repressing); every node has nonempty sources $\mathrm{S}(i)$ and targets $\mathrm{T}(i)$. Let $m_i=|\mathrm{T}(i)|$.

**Parameters.** For each node $i$:
- an *order parameter* is a bijection $\theta_i:\mathrm{T}(i)\to\{1,\dots,m_i\}$ (the order in which the thresholds of the out-edges of $i$ are crossed);
- a *logic parameter* is $h_i=(h_i^1,\dots,h_i^{m_i}):\mathbb{B}^{|\mathrm{S}(i)|}\to\mathbb{B}^{m_i}$ with each $h_i^k$ an increasing monotone Boolean function and the *ordering condition* $h_i^1(b)\succeq\cdots\succeq h_i^{m_i}(b)$ for all $b$.

Two parameters $(h_i,\theta_i)$, $(\hat h_i,\hat\theta_i)$ of node $i$ are adjacent if either $\theta_i=\hat\theta_i$ and exactly one component $h_i^j$ differs at exactly one input (logic adjacency), or $h_i=\hat h_i$ and $\theta_i,\hat\theta_i$ differ by swapping two consecutive values $k,k+1$ on which $h_i^k=h_i^{k+1}$ (order adjacency). The resulting factor graphs $\mathrm{PG}(i)$ combine into the *DSGRN parameter graph* $\mathrm{PG}=\prod_i\mathrm{PG}(i)$ (Cartesian product of graphs). Its size and shape depend only on in- and out-degrees, not on $\delta$.

**Multilevel dynamics.** For $p=(h,\theta)$ the state space is $\mathcal{D}=\prod_i\{0,1,\dots,m_i\}$. For an edge $(i,j)$ set $\mu_i^j(d_i)=1$ if $d_i\ge\theta_i(j)$ and $0$ otherwise, and let $B_i^j(d)=\mu_i^j(d_i)$ if $\delta(i,j)=1$ and $\neg\mu_i^j(d_i)$ if $\delta(i,j)=-1$. The multilevel update is

$$g_i(d)=\big|\{\,j\in\mathrm{T}(i): h_i^j(B^i(d))=1\,\}\big|\in\{0,\dots,m_i\},$$

and the *nearest neighbor asynchronous update* $\mathcal{G}:\mathcal{D}\rightrightarrows\mathcal{D}$ sets $\mathcal{G}(d)=\{d\}$ if $g(d)=d$, and otherwise moves one coordinate $i$ by one step $\pm1$ toward $g_i(d)$.

**Boolean parameters.** A monotone Boolean model $f$ for $RN$ corresponds to the $\prod_i m_i!$ parameter nodes with $h_i^j=\tilde h_i$ for all $j$, where $\tilde h_i$ is the increasing version of $f_i$ after composing with the edge signs; these form the *DSGRN Boolean parameter graph*, a proper subgraph of $\mathrm{PG}$.

**Wall labeling (Theorem 3.28).** Identifying each state $d$ with a top-dimensional cell of a cubical complex $\mathcal{X}$ and its left/right neighbors in direction $j$ with that cell's two $j$-walls, the labeling $\alpha(d,j,\lambda)=\operatorname{sign}(g_j(d)-d_j)$ (and $-\lambda$ when $g_j(d)=d_j$) transfers to a map $\omega$ on walls, and $\omega$ is a DSGRN wall labeling. Hence the combinatorial multilevel dynamics can be analyzed with the Morse graph machinery DSGRN uses for switching ODE models.

## Expansion

The order parameter records the relative position of the thresholds at which node $i$ starts to act on each of its targets, as in a steep-sigmoid or switching ODE. The state $d_i$ counts how many of those thresholds the concentration of $i$ exceeds, and $g_i(d)$ is the number of thresholds the target value of $x_i$ would exceed under the current inputs. Requiring the $h_i^k$ to be nested makes the target level monotone in the inputs. In the Boolean case every out-edge of $i$ switches at the same input, so all $m_i$ thresholds collapse together; multilevel parameters let different targets switch at different levels, which is how intermediate stable states and periodic orbits invisible to Boolean models appear. Computed examples (toggle-switch variants, three- and five-node networks, an epithelial-mesenchymal transition network) show the Boolean parameter graph missing higher-order multistability and stable oscillations present elsewhere in $\mathrm{PG}$.

## Sources

- Breschine Cummins, Marcio Gameiro, Tomas Gedeon, Konstantin Mischaikow, "Boolean models coarsely sample continuous dynamics of regulatory networks", arXiv:2606.14925 (2026), Definitions 3.6, 3.10-3.14, 3.19, 3.21-3.22 and Theorem 3.28 (Section 3), <https://doi.org/10.48550/arXiv.2606.14925>
