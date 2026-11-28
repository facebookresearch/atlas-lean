# Distribution of the total tree length via hyperbolic PDEs

**Ancestral process.** For a sample of size $n$ in a population whose inverse relative size (coalescent rate) at time $t$ in the past is a continuous function $\lambda(t)$, the number of ancestral lineages $A(t)$ is a time-inhomogeneous Markov chain on $\{1,\dots,n\}$ with $A(0)=n$ and generator $\lambda(t)Q$, where $Q_{k,k}=-\binom{k}{2}$, $Q_{k,k-1}=\binom{k}{2}$ and all other entries vanish. The accumulated tree length and the total tree length are

$$
L(t)=\int_0^t\mathbf 1_{\{A(s)>1\}}A(s)\,ds,\qquad \mathcal L=L(T_{MRCA}),\quad T_{MRCA}=\inf\{t:A(t)\le1\}.
$$

**Lemma.** With $F_k(t,x)=\mathbb{P}\{A(t)=k,\ L(t)\le x\}$, for all $x\ge0$ and $\bar t\ge x/2$,

$$
\mathbb{P}\{\mathcal L\le x\}=F_1(\bar t,x).
$$

**Corollary (marginal PDE).** The row vector $\mathbf F(t,x)=(F_1,\dots,F_n)(t,x)$ is, on $\{0<x<nt,\ t>0\}$, the strong solution of

$$
\partial_t\mathbf F(t,x)+\partial_x\mathbf F(t,x)\,V=\mathbf F(t,x)\,\lambda(t)Q,\qquad V=\mathrm{diag}(0,2,3,\dots,n),
$$

with boundary conditions $\mathbf F(t,nt)=\bigl(\mathbb{P}\{A(t)=1\},\dots,\mathbb{P}\{A(t)=n-1\},0\bigr)$ and $\mathbf F(t,0)=0$ for $t>0$.

**Two loci.** For two loci separated by at most one recombination event, let $\bar A(t)$ be the ancestral process with limited recombination, recording lineages ancestral to both loci, to the first only, to the second only, and the number of recombinations so far; let $L^a(t)$, $L^b(t)$ be the accumulated tree lengths at the two loci and $\mathcal L^a$, $\mathcal L^b$ the total lengths. Then for $\bar t\ge\max\{x,y\}/2$

$$
\mathbb{P}\{\mathcal L^a\le x,\ \mathcal L^b\le y\}=F_{(1,0,0,0)}(\bar t,x,y)+F_{(1,0,0,1)}(\bar t,x,y),
$$

where $F_s(t,x,y)=\mathbb{P}\{\bar A(t)=s,\ L^a(t)\le x,\ L^b(t)\le y\}$ and the two listed states are the absorbing ones. The vector $(F_s)_s$ solves on $\{0<x<nt,\ 0<y<nt,\ t>0\}$ the two-dimensional hyperbolic system $\partial_t\mathbf F+\partial_x\mathbf F\,V^a+\partial_y\mathbf F\,V^b=\mathbf F\,\bar Q(t)$, with $V^a$, $V^b$ the diagonal matrices of the numbers of lineages ancestral to each locus (set to zero once only one remains) and $\bar Q(t)$ the generator of $\bar A$.

## Depends on

- [Hyperbolic system for path integrals of a Markov chain](hyperbolic-system-for-path-integrals-of-a-markov-chain.md)

## Expansion

Since at least two lineages are present before the most recent common ancestor, $\mathcal L\ge2T_{MRCA}$; hence on $\{\mathcal L\le x\}$ the chain has been absorbed by time $x/2$ and the accumulated length has stopped growing, so the distribution of $\mathcal L$ is read off the absorbing component of the time-dependent joint distribution at any $\bar t\ge x/2$. The total tree length is the path integral of $v(k)=k\mathbf 1_{\{k>1\}}$ along the lineage-counting chain, so the general result for path integrals of Markov chains gives the transport–reaction system with speeds $0,2,\dots,n$, which is solved numerically along characteristics. The same argument with the two-dimensional path integral $(v^a,v^b)$ gives the joint law at two loci, the ingredient needed for transition probabilities between neighbouring genealogies in coalescent hidden Markov models.

## Sources

- Alexey Miroshnikov and Matthias Steinrücken, "Computing the joint distribution of the total tree length across loci in populations with variable size", *Theor. Popul. Biol.* 118 (2017), 1-19. <https://doi.org/10.1016/j.tpb.2017.09.002>
- Preprint version (the locators in this item follow its numbering): Alexey Miroshnikov, Matthias Steinrücken, *Computing the joint distribution of the total tree length across loci in populations with variable size*, arXiv (2016). Definitions 2.1, 2.3, 2.4, 2.6, 2.7; Lemma 3.1; Corollary 3.2; Lemma 3.4; Corollary 3.5. <https://doi.org/10.48550/arXiv.1609.08880>
