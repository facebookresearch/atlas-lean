# Genome share of initially advantaged ancestors in the biparental Moran model

**Model.** $N$ haploid hermaphroditic individuals. At each step two parents (mother and father) are drawn uniformly with replacement and produce one offspring, which replaces an individual chosen with probability proportional to its death weight: $1$ for advantaged individuals and $1 + s$ ($s > 0$) for others. At every locus the offspring inherits the allele of a uniformly chosen parent; the advantage is the mother's allele at the selected locus. Initially $Y_0 = \lfloor aN \rfloor$ individuals are advantaged. Given the pedigree, $W_n(i, j)$ is the probability that a gene of individual $i$ at time $n$ at an unlinked locus descends from ancestor $j$ at time $0$. Let $Y_n$ be the number of advantaged individuals and

$$U_n = \sum_{l \in \mathcal Y_n}\sum_{l' \in \mathcal Y_0} W_n(l, l'), \qquad V_n = \sum_{l \notin \mathcal Y_n}\sum_{l' \in \mathcal Y_0} W_n(l, l')$$

the genome mass from initially advantaged ancestors carried by advantaged and by disadvantaged individuals.

**Theorem.** Let $F(x) = x^{1+s}/(1-x)$. For $a \in (0,1)$ and every $c > 0$, $\sup_{t \le c}\bigl\|(Y_{\lfloor Nt\rfloor}, U_{\lfloor Nt\rfloor}, V_{\lfloor Nt\rfloor})/N - (y_t, u_t, v_t)\bigr\| \to 0$ in probability, where $y_t = F^{-1}\bigl(\frac{a^{1+s}}{1-a} e^{st}\bigr)$ and $(u_t, v_t)$ solve an explicit linear system driven by $y_t$. The advantaged type fixes with probability tending to $1$, and for $a < b < 1$, at the hitting time $T_{\lfloor bN \rfloor}$ of $\lfloor bN \rfloor$ advantaged individuals,

$$\frac{U_{T_{\lfloor bN\rfloor}}}{N} \to b\,\frac{a^{\frac{1+s}{2s}}}{(1-a)^{\frac{1}{2s}}}\left[\frac{(1-b)^{\frac{1}{2s}}}{b^{\frac{1+s}{2s}}} + \int_a^b \frac{(1-x)^{\frac{1}{2s}}}{x^{\frac{1+s}{2s}}}\Bigl(\frac12 + \frac{1}{2s}\frac{1}{1-x}\Bigr) dx\right]$$

in probability. The source proves this only for $b < 1$; it conjectures that the limit also holds at $b = 1$ (the fixation time), which would need a finer study of the variance of $U_n$, and does not prove it.

## Proof idea

The advantaged count $Y_n$ is a birth–death chain whose embedded jump chain is a biased random walk with up-probability $(1+s)/(2+s)$, so fixation is almost certain and takes $O(N)$ steps. Each event moves $O(1)$ genome mass between the advantaged and disadvantaged pools: a new advantaged offspring inherits half its genome from each parent, and deaths remove mass in proportion to the current pool composition. These increments average out, giving the ODE limit by a fluid-limit argument. Advantaged individuals transmit their whole genome, not only the selected allele, so the founders' share exceeds their initial frequency, with the excess decreasing in the fraction $a$ and increasing in $s$.

## Sources

- C. Coron and Y. Le Jan, "Genetic contribution of advantaged ancestors in the biparental Moran model–finite selection", Journal of Applied Probability (2026), 1–18, <https://doi.org/10.1017/jpr.2026.10137>. Numbering as in the preprint arXiv:2502.01178v3, <https://arxiv.org/abs/2502.01178v3>: Theorem 1.1, Corollary 1.2 and the remark after it, Propositions 2.2, 2.4 and 2.7.
