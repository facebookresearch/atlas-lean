# Split-sum sufficient condition for a split in the BHV Fréchet mean

**Setting.** $\mathbb T_n$ is BHV tree space of metric phylogenetic trees on $n$ leaves, a CAT(0) space glued from one non-negative orthant per tree topology, with coordinates the interior edge weights. For a split $s$ and tree $T$, $|s|_T$ is the weight of $s$ in $T$ ($0$ if absent). For a finite sample $\mathcal T=\{T_1,\dots,T_r\}$, $E(\mathcal T)$ is the set of splits occurring in some $T_i$, and $X(s)$ the set of splits incompatible with $s$. The Fréchet mean $\mu$ minimizes $\sum_i d(\mu,T_i)^2$ and is unique.

**Definition.** The *split sum* of $s$ for $\mathcal T$ is

$$\sigma(s,\mathcal T)=\sum_{T\in\mathcal T}|s|_T-\sum_{x\in E(\mathcal T)\cap X(s)}\ \sum_{T\in\mathcal T}|x|_T .$$

**Theorem.** If $s$ occurs in some tree of $\mathcal T$ and $\sigma(s,\mathcal T)>0$, i.e. the total weight of $s$ exceeds the total weight of all sample splits incompatible with $s$, then $s$ is a split of the Fréchet mean of $\mathcal T$. More precisely:
- if $s\in E(\mathcal T)$ is incompatible with some split of the mean, then $\sigma(s,\mathcal T)<0$;
- if $s\in E(\mathcal T)$ is compatible with all splits of the mean but not in it, then $\sigma(s,\mathcal T)\le0$.

**Remarks.** The condition is not necessary: there are four trees in $\mathbb T_5$ with no split of positive split sum whose mean is not the star tree, and two trees $T_1$ (one split $s_1$ of weight $6$) and $T_2$ (two splits of weights $3,4$, both incompatible with $s_1$) where $\sigma(s_1)=-1$. Every split of the mean occurs in some input tree, and a split occurring in some trees and compatible with all the others is always in the mean; along a split common to all trees the mean splits into the means of the two sides joined by an edge of averaged weight.

## Expansion

The proof uses the characterization of the Fréchet mean through the translated log map: at the true mean $\mu$, the log-map images of the sample trees must average to $\mu$ in the coordinates of $E(\mu)$ and have non-positive directional sums toward any compatible new split. For each tree, the geodesic from $\mu$ to $T$ has a support $(\mathcal A,\mathcal B)$, and a split of $\mu$ in block $A_j$ is mapped to $-\frac{\|B_j\|}{\|A_j\|}$ times its weight. If $s$ is incompatible with the mean, comparing coordinates shows that the weight of $s$ is outweighed by the norms $\|B_j\|$ of incompatible splits, which are bounded by their weight sums; if $s$ is compatible but absent, the directional-derivative condition gives the non-strict inequality. Together these are the contrapositive of the theorem.

## Sources

- M. Anaya, O. Anipchenko-Ulaj, A. Ashfaq, J. Chiu, M. Kaiser, M. S. Ohsawa, M. Owen, E. Pavlechko, K. St. John, S. Suleria, K. Thompson, C. Yap, "Properties for the Fréchet mean in Billera-Holmes-Vogtmann treespace", arXiv:1907.05937 (2019), <https://doi.org/10.48550/arXiv.1907.05937>. Section 2 (Proposition 1, Lemma 1, Theorems 1–4) and Section 3 (Lemmas 2–4, Theorem 5, Definition 8, Corollary 1, Examples 2 and 3).
