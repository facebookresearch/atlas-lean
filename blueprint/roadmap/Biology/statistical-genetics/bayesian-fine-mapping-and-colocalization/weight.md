# Unnormalized colocalization configuration weight

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants. The unnormalized weight of a [configuration](coloc-hypothesis-2.md) $S \in \iota_\ast \times \iota_\ast$ is

$$w(S) = \begin{cases} 1 & H(S) = H_0,\\ p_1 & H(S) = H_1,\\ p_2 & H(S) = H_2,\\ p_1 p_2 & H(S) = H_3,\\ p_{12} & H(S) = H_4, \end{cases}$$

where $H(S)$ is the colocalization hypothesis of $S$.
