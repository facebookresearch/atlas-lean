# Directional-derivative certificates for splits of the BHV Fréchet mean

**Setting.** Let $\mathbb{T}_N$ be Billera-Holmes-Vogtmann (BHV) space of rooted (or unrooted) metric phylogenetic trees with $N$ leaves, a CAT(0) space glued from orthants, one per tree topology. A tree $T$ has a set $E(T)$ of internal splits with positive lengths $|x|_T$ (set $|x|_T=0$ for $x\notin E(T)$). For a split $s$, $C(s)$ is the set of splits compatible with $s$, and $C(T)=\bigcap_{x\in E(T)}C(x)$. For a probability measure $P$ with finite second moment, the *Fréchet function* $F_P(T)=\tfrac12\int d(T,T')^2\,dP(T')$ is strictly convex with unique minimizer, the Fréchet mean $\mu$; for a finite sample $\mathcal{T}$ use the empirical measure.

**Statements.**
1. *(Optimality.)* For every direction $\sigma$ in the space of directions $\Sigma_T$ at $T$, $\nabla_\sigma F_P(T)=-\int d(T,T')\cos\angle_T(\sigma,T')\,dP(T')$, and $T$ is the Fréchet mean if and only if $\nabla_\sigma F_P(T)\ge 0$ for all $\sigma\in\Sigma_T$.
2. *(Split certificate.)* Let $T$ lie in an orthant of codimension $0\le l<N-2$ with $E(T)\subset E(\mu)$ and $\mu$ not in that orthant, and let $s\in C(T)\setminus E(T)$ with direction $\sigma_s$ (growing the edge $s$). If $\nabla_{\sigma_s}F_P(T)<0$, then $s\in E(\mu)$. Equivalently, an angle $\angle_T(\mu,\sigma_s)\ge\pi/2$ forces $\nabla_{\sigma_s}F_P(T)\ge 0$.
3. *(Sample criterion.)* For a finite sample $\mathcal{T}$ with Fréchet mean $\hat\mu$, a split $s$ belongs to $E(\hat\mu)$ whenever

$$\sum_{T\in\mathcal{T}}\sqrt{\sum_{x\in E(T),\,x\notin C(s)}|x|_T^2}\;<\;\sum_{T\in\mathcal{T}}|s|_T ,$$

i.e. the total length of $s$ across the sample exceeds the summed root-square lengths of the splits incompatible with it.
4. *(Oscillation of Sturm's algorithm.)* If the sample mean lies in a stratum $\mathcal{O}$ of codimension $l\ge 1$ and some sample tree has a split in $C(\hat\mu)\setminus E(\hat\mu)$, then the iterates of Sturm's algorithm (move toward a uniformly drawn sample tree by step $1/(j+1)$) leave $\mathcal{O}$ infinitely often with probability $1$.

## Expansion

Starting at the star tree $T$ (or at a tree whose splits are already known to be in $\mu$), the derivative in the direction of a new split $s$ is $-\sum_{T'}d(T,T')\cos\angle$; the geodesic from $T$ to a sample tree containing $s$ uses the direction $\sigma_s$ with cosine $|s|_{T'}/d$, while a tree with splits incompatible with $s$ contributes at most the root-square length of those splits. Comparing the two sums gives a negative derivative, and convexity of $F$ along geodesics with the angle bound in statement 2 implies that the mean must contain $s$. Iterating with the found splits builds the topology of the mean edge by edge, after which the mean can be computed within a fixed orthant. The tangent cone at a lower-stratum point decomposes as a product of a Euclidean factor and smaller BHV spaces, so the checks factor over components.

## Sources

- Lars Lammers, Tom M. W. Nye, Stephan F. Huckemann, "Statistics for Phylogenetic Trees in the Presence of Stickiness", arXiv:2407.03977 (2024), Theorems 2.15, 2.17, 3.1 and 3.7, Corollary 3.3, <https://doi.org/10.48550/arXiv.2407.03977>.
