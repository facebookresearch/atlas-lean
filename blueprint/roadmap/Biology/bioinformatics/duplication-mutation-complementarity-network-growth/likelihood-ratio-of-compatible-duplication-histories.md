# Likelihood ratio of compatible duplication histories in the DMC model

**Duplication–mutation with complementarity (DMC) model.** With parameters $p, p_c \in [0,1]$, a protein interaction network $G_t$ is obtained from $G_{t-1}$ by: (1) *duplication*: choose an anchor node $u_t$ uniformly and add a duplicate $v_t$ joined to every neighbor of $u_t$; (2) *mutation*: for each neighbor $w$ of $u_t$, pick one of the edges $(u_t,w)$, $(v_t,w)$ with probability $1/2$ each and delete it with probability $1-p$; (3) *complementarity*: join $u_t$ and $v_t$ with probability $p_c$.

A growth history of an observed network $G$ is a sequence $(G_0,\dots,G_n = G)$ of single DMC steps. Given the **duplication forest** $\Gamma$ of $G$ (paralog relationships), a node sequence $\theta = (v_1,\dots,v_n)$ is *compatible* with $\Gamma$ if each $v_t$ lies in a cherry of the forest $\Gamma^\theta_t$ obtained by successively merging $v_n, v_{n-1},\dots$ into their cherry siblings; the sibling is the anchor $u_t$. A compatible $\theta$ determines a unique history $G^\theta_n = G, G^\theta_{n-1},\dots,G^\theta_0$ (merging $v_t$ into $u_t$ adds the edges $(w,u_t)$ for neighbors $w$ of $v_t$ not already adjacent to $u_t$), with likelihood

$$L(\theta \mid G,\Gamma,\mathcal M) = \prod_{i=1}^{n} \Pr\big(G^\theta_i \mid G^\theta_{i-1},\Gamma,\mathcal M\big).$$

For each step let $\delta(v_i) \in \{0,1\}$ indicate whether $v_i \sim u_i$, let $\alpha(v_i)$ be the number of common neighbors of $v_i$ and $u_i$, and let $\beta(v_i)$ be the number of nodes adjacent to exactly one of $v_i, u_i$ in $G^\theta_i$. Write $\delta(\theta), \alpha(\theta), \beta(\theta)$ for the sums over $i$ (complementarity, extension and loss numbers).

**Theorem.** Let $\theta_1,\theta_2$ be compatible with $\Gamma$. Then:

1. the seed graphs $G^{\theta_1}_0$ and $G^{\theta_2}_0$ are isomorphic;
2. $\delta(\theta_1) = \delta(\theta_2)$ and $\alpha(\theta_1) = \alpha(\theta_2)$;
3. the likelihood ratio is

$$\frac{L(\theta_1 \mid G,\mathcal M,\Gamma)}{L(\theta_2 \mid G,\mathcal M,\Gamma)} = \Big(\frac{1-p}{2}\Big)^{\beta(\theta_1) - \beta(\theta_2)}.$$

Hence for any $p < 1$ the most probable history is the compatible sequence with the smallest loss number, independently of $p$ and $p_c$.

## Expansion

Given the anchor, the one-step probability factorizes over neighbors: a shared neighbor survives both mutations with probability $p$, a neighbor kept by exactly one of the two nodes has probability $(1-p)/2$, and the anchor–duplicate edge contributes $p_c$ or $1-p_c$; uniform anchor choice contributes a factor depending only on graph sizes, which are the same for all compatible sequences. Adjacent compatible sequences differ by swapping two positions, and the swap changes only two intermediate graphs, so the complementarity and extension numbers are invariant; iterating swaps connects all compatible sequences. Only the loss factors $((1-p)/2)^{\beta}$ remain in the ratio, reducing history inference to a combinatorial minimization of $\beta(\theta)$.

## Sources

- Si Li, Kwok Pui Choi, Taoyang Wu, Louxin Zhang, "Reconstruction of network evolutionary history from extant network topology and duplication history", arXiv (2012). Section 2 (DMC model, backward operator, compatibility) and the theoretical results subsection (seed-graph lemma, invariance and likelihood-ratio theorems). <https://doi.org/10.48550/arXiv.1203.2430>. Published version: Bioinformatics Research and Applications (ISBRA 2012), Lecture Notes in Computer Science 7292 (2012), 165–176, <https://doi.org/10.1007/978-3-642-30191-9_16>; locators above refer to the arXiv version.
