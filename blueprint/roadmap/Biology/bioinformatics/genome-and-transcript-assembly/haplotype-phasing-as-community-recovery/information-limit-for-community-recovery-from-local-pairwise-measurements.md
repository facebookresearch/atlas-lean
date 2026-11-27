# Information limit for community recovery from local pairwise measurements

**Model.** Each of $n$ vertices carries an unknown binary label $X_i\in\{0,1\}$ (in haplotype phasing: which parental chromosome carries the minor allele at SNP $i$). A measurement graph $\mathcal G$ specifies which pairs can be measured; for each edge $(i,j)$ of $\mathcal G$ an independent $\mathrm{Poisson}(\lambda)$ number of measurements is taken, so that $m=\lambda|E(\mathcal G)|$ is the expected total number of measurements, and each measurement returns $X_i\oplus X_j$ flipped independently with probability $\theta\in(0,\tfrac12)$. In the **ring** $\mathcal R_r$ with locality radius $r$, vertices sit on a cycle and $i\sim j$ iff their cyclic distance is at most $r$ (reads only link nearby SNPs). Exact recovery means outputting $X$ up to a global flip. Let $\mathrm{KL}(0.5\,\|\,\theta)$ be the Kullback–Leibler divergence between Bernoulli($0.5$) and Bernoulli($\theta$).

**Theorem (rings).** Fix $\theta$ and $\epsilon>0$ and set

$$m^*=\frac{n\log n}{2\left(1-e^{-\mathrm{KL}(0.5\|\theta)}\right)}.$$

If $m\ge(1+\epsilon)m^*$, two nearly linear-time spectral-plus-local-refinement algorithms recover $X$ exactly with probability tending to one (within $O(\log n)$ refinement iterations), provided $r\gtrsim\log^3 n$ (for the expansion-based algorithm) or $r\ge n^{\delta}$ for some $\delta>0$ (for the stitching algorithm). Conversely, if $m<(1-\epsilon)m^*$, every algorithm fails with probability tending to one.

**Other locality structures.** The same sharp threshold holds with

$$m^*=\frac{\max\{\tfrac12,\beta\}\,n\log n}{1-e^{-\mathrm{KL}(0.5\|\theta)}}\quad\text{(lines, } r=n^\beta,\ 0<\beta<1),\qquad m^*=\frac{\max\{\tfrac12,4\beta\}\,n\log n}{1-e^{-\mathrm{KL}(0.5\|\theta)}}\quad\text{(grids, } r=n^\beta,\ 0<\beta<\tfrac12).$$

For $L$-wise measurements (e.g. linked reads covering $L$ SNPs, each vertex read with error rate $p$) the threshold becomes $m^*=\frac{n\log n}{L(1-e^{-D(P_0,P_1)})}$, where $D$ is the Chernoff-type information between $P_0=(1-p)\,\mathrm{Bin}(L-1,p)+p\,\mathrm{Bin}(L-1,1-p)$ and $P_1=p\,\mathrm{Bin}(L-1,p)+(1-p)\,\mathrm{Bin}(L-1,1-p)$.

## Expansion

The converse is a local argument: exact recovery fails as soon as some vertex has more of its measurements corrupted than not, and the probability that a vertex with $d$ incident measurements is in this state is about $e^{-d(1-e^{-\mathrm{KL}(0.5\|\theta)})}$ to leading exponential order; a union over $n$ roughly independent vertices gives the $n\log n$ scaling, with the max-terms for lines and grids reflecting boundary vertices that have fewer neighbors. Achievability first recovers a small core by spectral methods, propagates labels along the local graph with majority votes, and then runs iterative majority refinement, which contracts the number of errors in every neighborhood by half per round.

## Sources

- Yuxin Chen, Govinda Kamath, Changho Suh, David Tse, "Community Recovery in Graphs with Locality", ICML 2016, PMLR 48 (sampling model of §2.1 and the theorems for rings, lines and grids); preprint arXiv:1602.03828 (2016), Theorems 1–2 and 5, <https://doi.org/10.48550/arXiv.1602.03828>.
