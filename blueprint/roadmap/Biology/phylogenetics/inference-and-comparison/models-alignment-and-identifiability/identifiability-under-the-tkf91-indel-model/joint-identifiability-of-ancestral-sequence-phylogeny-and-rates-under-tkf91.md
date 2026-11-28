# Joint identifiability of ancestral sequence, phylogeny and rates under the TKF91 model

**Model (binary TKF91-type indel process).** Sequences are words over $\{0,1\}$ (or empty). With parameters $\lambda, \mu, \nu > 0$, $\lambda \ne \mu$, and a distribution $(\pi_0,\pi_1)$: each digit is substituted at rate $\nu$ by a digit drawn from $\pi$; each digit is deleted at rate $\mu$; and each digit gives birth at rate $\lambda$ to a new digit, drawn from $\pi$, inserted immediately to its right. On a rooted phylogeny $T$ with edge lengths, the root carries an unknown sequence $\vec x$ of length $M$ and the process runs independently along branches; $\mathcal{I}_u$ denotes the sequence at leaf $u$ and $t_u$ the root-to-leaf distance.

**Theorem.**

1. The topology of $T$ and all edge lengths up to the common factor $\mu$ are identifiable from the joint laws of pairwise sequence *lengths* $\{\mathcal{L}(|\mathcal{I}_u|,|\mathcal{I}_v|)\}_{u,v}$ at the leaves.
2. Suppose $M \ge 1$ (for $M = 0$ every leaf sequence is empty and all three moments vanish). For each leaf $u$, $(\mu t_u, \lambda t_u)$ is identifiable from the law of $\mathcal{I}_u$; in fact the map $(M, \mu t, \lambda t) \mapsto (\mathbb{E}_M|\mathcal{I}_t|, \mathbb{E}_M|\mathcal{I}_t|^2, \mathbb{E}_M|\mathcal{I}_t|^3)$ is one-to-one with an inverse not depending on any unknown.
3. If $\pi_0$ is known, the ancestral sequence $\vec x$ itself and $\nu t_u$ are identifiable from the law of $\mathcal{I}_u$ at any single leaf.

**Distance formula.** For leaves $u,v$ with lengths $L^u = |\mathcal{I}_u|$, $L^v = |\mathcal{I}_v|$ and path distance $t_{uv}$,

$$e^{-\frac{\mu-\lambda}{2}t_{uv}} = \frac{\mu-\lambda}{M(\lambda+\mu)}\,e^{\frac{\mu-\lambda}{2}(t_u+t_v)}\operatorname{Cov}_M(L^u,L^v) + e^{-\frac{\mu-\lambda}{2}(t_u+t_v)},$$

and the most recent common ancestor $w$ of $u,v$ has depth $t_w = (t_u + t_v - t_{uv})/2$.

**Special case $\lambda = \mu$.** If it is known that $\lambda = \mu$, then $M = \mathbb{E}_M|\mathcal{I}_t|$ and, for $M \ge 1$, $\mu t = \dfrac{\mathbb{E}_M|\mathcal{I}_t|^2 - M^2}{2M}$: the length is then a critical linear birth–death process, with $\mathbb{E}_M|\mathcal{I}_t|^2 = M^2 + 2\mu M t$.

## Expansion

Ignoring digits, sequence length is a linear birth–death process with immigration-free rates $\lambda$ and $\mu$ per site, started from $M$ independent sites, so its first three moments are explicit functions of $(M, e^{-(\mu-\lambda)t}, \lambda/\mu)$ and can be inverted in closed form. Lengths at two leaves are independent given the length at their common ancestor, so their covariance depends on the shared path only through $e^{-(\mu-\lambda)t_w}$; this yields tree metrics and hence topology and branch lengths. The probability generating function of the 1-mer counts (numbers of 1s and 0s) factorizes over ancestral sites as $r_1^a r_2^b$, which identifies the number $a$ of ancestral 1s and $\nu t$; finally the probabilities $p^\sigma_{\vec x}(s)$ that the first digit is $\sigma$ at an increasing sequence of times give a triangular linear system recovering the digits of $\vec x$ one by one.

## Sources

- Alex Xue, Brandon Legried and Wai-Tong Louis Fan, "Joint Identifiability of Ancestral Sequence, Phylogeny, and Mutation Rates Under an Indel Model", Journal of Computational Biology (2026), 15578666261504447, <https://doi.org/10.1177/15578666261504447>; numbering as in arXiv:2410.09620: Definition 1, Theorems 1–5 and Propositions 1–4.
