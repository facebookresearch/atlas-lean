# Robust reconstruction of circular split networks from distorted metrics

**Setting.** A *split* of a taxon set $X$ is an unordered bipartition $\{S_1,S_2\}$ into non-empty parts. A weighted split network $N=(X,\mathcal{S},w)$ has distinct splits with weights $w(S)>0$; it is *circular* if for some ordering $x_1,\dots,x_n$ of $X$ every split separates a contiguous block $\{x_p,\dots,x_q\}$ from the rest. Two splits are *compatible* if one of the four part intersections is empty. For $x,y\in X$ let $\mathcal{S}|_{x,y}$ be the splits separating them, and for a set $\mathcal{A}$ of splits let $d(x,y;\mathcal{A})=\sum_{S\in\mathcal{S}|_{x,y}\cap\mathcal{A}}w(S)$; the network metric is $d=d(\cdot,\cdot;\mathcal{S})$. Define

- the *minimum weight* $\epsilon_N=\min_S w(S)$;
- the *chord depth* $\Delta_N=\max_S\min\{d(x,y;\mathcal{C}(S)):S\in\mathcal{S}|_{x,y}\}$, where $\mathcal{C}(S)$ is the set of splits compatible with $S$;
- the *maximum incompatibility* $\Omega_N=\max_S\sum_{S'\in\mathcal{I}(S)}w(S')$, where $\mathcal{I}(S)$ is the set of splits incompatible with $S$.

A dissimilarity $\hat d$ is a $(\tau,R)$-*distorted metric* of $N$ if $|d(x,y)-\hat d(x,y)|<\tau$ whenever $d(x,y)<R+\tau$ or $\hat d(x,y)<R+\tau$: estimates are accurate only on short distances, as with distances estimated from finite DNA sequences.

**Theorem.** Let $N$ be a circular network. Given a $(\tau,R)$-distorted metric $\hat d$ with

$$\tau<\tfrac14\epsilon_N\qquad\text{and}\qquad R>3\Delta_N+7\Omega_N+\tfrac52\epsilon_N,$$

the split set $\mathcal{S}$ can be reconstructed in polynomial time, together with weight estimates satisfying $|\hat w(S)-w(S)|<2\tau$ for every split.

The linear dependence on $\Omega_N$ is necessary: there are pairs of distinct circular networks, with all split weights $1$, that cannot be distinguished from a distorted metric whose accuracy radius is sublinear in the maximum incompatibility. Together with the known necessity of linear dependence on depth in the tree case, this shows the radius condition is of the right form.

## Expansion

The algorithm works locally. For every pair $x,y$ with $\hat d(x,y)\le\Delta+\Omega+\tau$, it takes the ball of taxa near the pair, where all distances are accurately estimated, and reconstructs the circular split system restricted to that ball by isolation indices: a split's isolation index $\alpha_d(S)$, the minimum over quartets across $S$ of a four-point-condition gap, recovers its weight on a circular split system. These *mini reconstructions* are then extended to bipartitions of all of $X$ by assigning each far taxon to the side indicated by short-distance comparisons. Correctness of the mini reconstructions, correctness of the extension, and exhaustivity (every split of $N$ has a witnessing pair within distance $\Delta+\Omega+\tau$, because $d(x,y)=d(x,y;\mathcal{C}(S))+d(x,y;\mathcal{I}(S))$) give $\hat{\mathcal{S}}=\mathcal{S}$, and the weight bound follows from the $\tau$-accuracy of the quartet sums. Unlike Neighbor-Net, which uses all distances, the method never relies on long, unreliable distance estimates.

## Sources

- Sebastien Roch, Kun-Chieh Wang, "Circular Networks from Distorted Metrics", arXiv:1707.05722 (2017): Section 1.1 (split networks, compatibility, circularity, isolation index, distorted metrics), Section 1.2 (minimum weight, chord depth, maximum incompatibility; main reconstruction theorem and the lower-bound example), Section 3 (propositions on mini reconstruction, bipartition extension, exhaustivity and weight estimates). <https://doi.org/10.48550/arXiv.1707.05722> Published version: Lecture Notes in Computer Science (2018) 167–176, <https://doi.org/10.1007/978-3-319-89929-9_11>.
