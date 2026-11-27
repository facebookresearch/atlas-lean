# Closest network proximity and its degree-matched z-score

**Setting.** Let $G = (V, E)$ be a connected undirected graph (the human interactome) with shortest-path distance $d : V \times V \to \mathbb{Z}_{\ge 0}$. Let $C \subseteq V$ be a nonempty disease module (host genes associated with a disease) and $T \subseteq V$ a nonempty drug-target set.

**Definition (closest proximity).**

$$\langle d_{CT} \rangle = \frac{1}{|C| + |T|}\left( \sum_{c \in C} \min_{t \in T} d(c,t) + \sum_{t \in T} \min_{c \in C} d(c,t) \right).$$

**Definition (z-score).** Draw $B$ random pairs $(C_b, T_b)$ of vertex sets whose degree distributions match those of $C$ and $T$, and let $\bar d_r$ and $\sigma_r$ be the mean and standard deviation of $\langle d_{C_b T_b}\rangle$ over $b = 1, \dots, B$. Then

$$Z_{d_{CT}} = \frac{\langle d_{CT}\rangle - \bar d_r}{\sigma_r}.$$

The z-score is defined when $\sigma_r > 0$. The randomized proximities can be constant, for example when $C$ and $T$ are both the whole vertex set, so that every degree-matched draw returns the same sets; then no z-score is computed.

A drug is called proximal to the module when $Z < -1.5$ and the empirical permutation $p$-value is below $0.05$ (with $B = 1000$ in the source).

**Basic properties.** $\langle d_{CT}\rangle$ is symmetric in $C$ and $T$; it is $0$ if and only if $C = T$; and it is at most the diameter of $G$.

## Remarks

Each vertex contributes its distance to the nearest vertex of the other set, so $\langle d_{CT}\rangle = 0$ forces every element of $C$ to lie in $T$ and conversely. Raw proximity is confounded by degree, because hubs are close to everything; matching degrees in the null removes this bias, which is why the z-score rather than $\langle d_{CT}\rangle$ is thresholded. The source applies this to 119 pooled coronavirus host proteins and over 2000 drugs, finding 135 proximal drugs.

## Sources

- Y. Zhou, Y. Hou, J. Shen, Y. Huang, W. Martin and F. Cheng, *Network-based drug repurposing for novel coronavirus 2019-nCoV/SARS-CoV-2*, Cell Discov. 6 (2020), 14. <https://doi.org/10.1038/s41421-020-0153-3> (PMCID: PMC7073332). Methods, "Network proximity measure", Eqs. (1)–(2).
- E. Guney, J. Menche, M. Vidal and A.-L. Barabási, *Network-based in silico drug efficacy screening*, Nat. Commun. 7 (2016), 10331. <https://doi.org/10.1038/ncomms10331>
