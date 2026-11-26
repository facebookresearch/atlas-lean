# Equidistribution and Poisson limit of stacked pairs and minimal pseudoknots in matchings

**Setting.** A *matching* of size $n$ is a perfect matching of the points $1,\dots,2n$ into $n$ arcs. It models an RNA secondary structure with arbitrary pseudoknots, with arcs as base pairs. An **endhered pattern** of size $p$ is a set of $p$ arcs whose starting points are consecutive, $i+1,\dots,i+p$, and whose ending points are consecutive, $j+1,\dots,j+p$. Such a pattern is encoded by the permutation $\pi\in S_p$ that records which start is joined to which end. The pattern $21$ consists of arcs $(i+1,j+2)$ and $(i+2,j+1)$: two nested consecutive arcs, i.e. a *stacked base pair*. The pattern $12$ consists of arcs $(i+1,j+1)$ and $(i+2,j+2)$: two crossing consecutive arcs, the *minimal pseudoknot*. Let $a_{n,k}$ be the number of matchings of size $n$ with exactly $k$ occurrences of $21$.

**Theorem.**

*(1)* (Symmetry) For every $p$ the joint distribution of the patterns $12\cdots p$ and $p\cdots21$ over matchings of size $n$ is symmetric. In particular, $12$ and $21$ are equidistributed, and the number of matchings with $k$ copies of $21$ and $m$ of $12$ equals the number with $m$ copies of $21$ and $k$ of $12$.

*(2)* (Recurrence) $a_{1,0}=1$, $a_{1,k}=0$ for $k\ne0$, and

$$a_{n+1,k}=a_{n,k-1}+2(n-k)\,a_{n,k}+2(k+1)\,a_{n,k+1}.$$

Consequently $a_{n+1,0}=2na_{n,0}+2(n-1)a_{n-1,0}$ with $a_{2,0}=2$, and $a_{n+1,1}=2n(a_{n,1}+a_{n-1,1})$ with $a_{2,1}=1$.

*(3)* (Asymptotics) For each fixed $k$, as $n\to\infty$,

$$a_{n,k}\sim\frac{1}{2^kk!}\Big(\frac2e\Big)^{n+1/2}n^n,\qquad\frac{a_{n,k}}{a_{n,k+1}}\to2(k+1).$$

*(4)* (Poisson limit) In a uniformly random matching of size $n$, the number of occurrences of $21$ (and likewise of $12$) converges in distribution to $\mathrm{Poisson}(1/2)$.

## Expansion

The total number of matchings is $(2n-1)!!\sim\sqrt2\,(2/e)^nn^n$, so item 3 says that the proportion of matchings with $k$ stacked pairs tends to $e^{-1/2}(1/2)^k/k!$. Heuristically, there are about $n^2/2$ candidate position pairs $(i,j)$, each carrying a given pattern of size 2 with probability about $1/(2n)^2$, giving mean $\tfrac12$ and asymptotically independent rare events. The recurrence comes from inserting a new arc at the start of a matching of size $n$ and tracking whether it creates or destroys an occurrence. The endhered twist (reversing runs of consecutive starts or ends) exchanges increasing and decreasing patterns, which proves the symmetry. In native RNA structures with pseudoknots, stacked pairs vastly outnumber minimal pseudoknots. Measured against the uniform null model, which treats the two patterns symmetrically, this asymmetry quantifies the energetic preference for helices.

## Sources

- Célia Biane, Greg Hampikian, Sergey Kirgizov, Khaydar Nurligareev, "Endhered patterns in matchings and RNA", arXiv:2404.18802 (2024), Definition 2.1 (endhered patterns), Corollary 2.6, Theorem 2.8, Corollaries 2.10 and 2.12, Theorem 2.16, Corollaries 2.18–2.19, <https://doi.org/10.48550/arXiv.2404.18802>.
