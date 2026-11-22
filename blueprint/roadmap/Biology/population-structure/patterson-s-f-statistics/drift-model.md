# Admixture-graph drift model

Let $\mu$ be a measure on a measurable space $\Omega$, let $E$ be a finite set (the edges of a graph) and $P$ a set (the populations). A drift model consists of

- a real function $r$ on $\Omega$ (the ancestral, root, allele frequency), square integrable;
- for each edge $e$, a real function $\delta_e$ on $\Omega$ (the drift increment along $e$), square integrable, and a real number $\ell_e$ (the drift length of $e$);
- for each population $X$ and edge $e$, a real number $w(X, e)$ (the lineage weight),

such that $\int \delta_e \delta_f \, d\mu = 0$ for $e \ne f$ and $\int \delta_e^2 \, d\mu = \ell_e$ for every $e$.

On an admixture graph, $w(X, e)$ is the sum, over root-to-$X$ paths through $e$, of the products of the admixture proportions along the path; on a tree it is $1$ if $e$ lies on the root-to-$X$ lineage and $0$ otherwise. Only second moments are imposed, as they are all that f-statistics see.
