# Optimal extinction probability of amplifiers of selection in the Moran process

**Moran process on a graph.** Let $G$ be a connected graph or strongly connected digraph on $n\ge2$ vertices, each occupied by one individual. Mutants have fitness $r>1$, non-mutants fitness $1$. Initially one vertex, chosen uniformly at random, is a mutant. At each step an individual is chosen to reproduce with probability proportional to its fitness, and its offspring replaces the occupant of a uniformly random out-neighbour. The process ends in *fixation* (all mutants) or *extinction* (no mutants). Write $\ell_r(G)$ for the extinction probability. A family of graphs is *strongly amplifying* if $\ell_r(G)\to0$ as $n\to\infty$; on the complete graph $\ell_r\to1/r$, and on large stars $\ell_r\to1/r^2$.

**Theorem.** Fix $r>1$.

1. (Digraph lower bound.) Every strongly connected $n$-vertex digraph satisfies $\ell_r(G)>1/(5rn^{1/2})$. Hence the megastar family, with extinction probability $O(n^{-1/2}\log^{23}n)$, is optimal up to logarithmic factors.
2. (Undirected lower bound.) Every connected $n$-vertex undirected graph satisfies $\ell_r(G)>1/(42\,r^{4/3}n^{1/3})$.
3. (Dense incubators.) There is an infinite family $\mathcal{D}_r$ of connected undirected graphs with $\ell_r(G)\le71/(r(r-1)^2n)^{1/3}$ for every $G\in\mathcal{D}_r$ with $n$ vertices, matching item 2 up to constants. A dense incubator consists of $k$ stars, each with $\lceil r\sqrt{\beta k}\rceil$ leaves, together with a clique of size $\beta k$ joined to every star centre ($k$ a perfect square, $\beta$ a constant depending on $r$); it has $\Theta(n^{4/3})$ edges.
4. (Edge-density tradeoff.) Every connected undirected graph with $n$ vertices and $m$ edges has $\ell_r(G)\ge n/(288\,r^2m)$, and sparse incubators with any prescribed density in the admissible range achieve $\ell_r(G)\le2^{14}rn/((r-1)^2m)$, so $\Theta(n/m)$ is the optimal extinction probability at edge count $m$.

Population structure can thus push the probability that a single advantageous mutant is lost from the constant $1/r$ of a well-mixed population down to order $n^{-1/2}$ (directed) or $n^{-1/3}$ (undirected), and no further.

## Expansion

1. Lower bounds: the initial mutant dies before reproducing with probability at least the chance that one of its in-neighbours reproduces onto it first. Averaging over the uniformly random start, a vertex of large in-degree weight is rarely chosen and a vertex of small weight is quickly overwritten; optimizing this tradeoff over all digraphs gives $n^{-1/2}$.
2. In undirected graphs reproduction weights are tied to degrees in both directions, which costs an extra power and gives $n^{-1/3}$, and $n/m$ in terms of the edge count.
3. Upper bounds: a mutant starting on a star leaf (most vertices are leaves) is rarely replaced because its centre is busy; once it captures the centre it seeds the clique, which then floods all other star centres and leaves.

## Sources

- Leslie Ann Goldberg, John Lapinskas, Johannes Lengler, Florian Meier, Konstantinos Panagiotou and Pascal Pfister, *Asymptotically optimal amplifiers for the Moran process*, arXiv:1611.04209 (Theorems 1, 2, 3, 6 and 7). <https://doi.org/10.48550/arXiv.1611.04209> Published version: Theoretical Computer Science 758 (2019) 73–93, <https://doi.org/10.1016/j.tcs.2018.08.005>.
- E. Lieberman, C. Hauert, M. A. Nowak, Evolutionary dynamics on graphs, *Nature* 433 (2005), 312–316. <https://doi.org/10.1038/nature03204>
