# Normalized categorical colocalization prior

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, with [null mass](p0.md) $p_0$. The categorical prior of a [configuration](coloc-hypothesis-2.md) $S \in \iota_\ast \times \iota_\ast$ is

$$\pi(S) = \begin{cases} p_0 & H(S) = H_0,\\ p_1 & H(S) = H_1,\\ p_2 & H(S) = H_2,\\ p_1 p_2 & H(S) = H_3,\\ p_{12} & H(S) = H_4, \end{cases}$$

where $H(S)$ is the colocalization hypothesis of $S$. It is a probability distribution on configurations, distinct from the unnormalized [configuration weights](weight.md), which give $H_0$ weight $1$.
