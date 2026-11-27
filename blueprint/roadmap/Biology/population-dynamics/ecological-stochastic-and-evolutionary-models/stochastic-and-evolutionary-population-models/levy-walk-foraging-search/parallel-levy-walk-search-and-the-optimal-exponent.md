# Parallel Lévy walk search and the optimal exponent

**Model.** A *Lévy walk* on $\mathbb{Z}^2$ with exponent $\alpha\in(1,\infty)$ moves in jump-phases. At the start of each phase, at node $u$, it draws a jump length $d$ with

$$\Pr(d=0)=\tfrac12,\qquad \Pr(d=i)=c_\alpha\, i^{-\alpha}\quad(i\ge1),$$

so that $\Pr(d\ge i)=\Theta(i^{1-\alpha})$. It then picks a node $v$ uniformly among the nodes at $\ell_1$-distance $d$ from $u$, and travels to $v$ in $d$ unit steps along a uniformly random monotone (direct) lattice path. If $d=0$ it stays put for one step. Unlike a Lévy flight, which jumps directly to $v$, the walk visits every node on its path. For a target $z\in\mathbb{Z}^2$ with $\ell=\|z\|_1$, let $\tau_\alpha(z)$ be the hitting time of one walk started at the origin. For $k$ independent walks started together at the origin, let $\tau^k_\alpha(z)$ be the first step at which some walk visits $z$. This models central-place foraging by $k$ animals around a nest, motivated by the Lévy foraging hypothesis.

**Theorem (single walk, constant $\alpha$, $\ell\to\infty$).**
- *Super-diffusive*, $\alpha\in(2,3)$: $\Pr(\tau_\alpha(z)=O(\ell^{\alpha-1}))=\Omega(1/(\ell^{3-\alpha}\log^2\ell))$; $\Pr(\tau_\alpha(z)\le t)=O(t^2/\ell^{\alpha+1})$ for $\ell\le t=O(\ell^{\alpha-1})$; and $\Pr(\tau_\alpha(z)<\infty)=O(\log\ell/\ell^{3-\alpha})$.
- *Diffusive*, $\alpha\ge3$: $\Pr(\tau_\alpha(z)=O(\ell^2\log^2\ell))=\Omega(1/\log^4\ell)$, and $\Pr(\tau_\alpha(z)\le t)=O(t^2\log\ell/\ell^4)$ for $\ell\le t=O(\ell^2)$.
- *Ballistic*, $\alpha\in(1,2]$: $\Pr(\tau_\alpha(z)=O(\ell))=\Omega(1/(\ell\log\ell))$, and $\Pr(\tau_\alpha(z)<\infty)=O(\log^2\ell/\ell)$.

**Theorem (parallel walks, tuned exponent).**
- If $\log^6\ell\le k\le\ell\log^4\ell$ and $\alpha=3-\frac{\log k}{\log\ell}+5\frac{\log\log\ell}{\log\ell}$, then $\tau^k_\alpha(z)=O(\ell^2\log^6\ell/k)$ with probability $1-e^{-\omega(\log\ell)}$.
- If $k=\omega(\log^5\ell)$, then $\tau^k_3(z)=O(\ell^2)$ with probability $1-e^{-\omega(\log\ell)}$.
- If $k=\omega(\ell\log^2\ell)$, then $\tau^k_2(z)=O(\ell)$ with probability $1-e^{-\omega(\log\ell)}$.

For $\mathrm{polylog}\,\ell\le k\le\ell\,\mathrm{polylog}\,\ell$, the optimal exponent is unique and equals $\alpha_{k,\ell}=3-\frac{\log k}{\log\ell}+O\!\big(\frac{\log\log\ell}{\log\ell}\big)\in(2,3)$. Shifting $\alpha$ by any constant either multiplies the hitting time by a polynomial factor in $\ell$ or makes all walks miss $z$ with probability $1-o(1)$.

**Theorem (random exponents).** Suppose each of $k\ge\log^8\ell$ walks draws its exponent independently and uniformly from $(2,3)$, with no knowledge of $k$ or $\ell$. Then

$$\Pr\Big(\tau^k_{\mathrm{rand}}(z)=O\big((\ell^2/k)\log^7\ell+\ell\log^3\ell\big)\Big)=1-e^{-\omega(\log\ell)}.$$

This matches, up to polylogarithmic factors, the universal lower bound $\Omega(\ell^2/k+\ell)$ for any search strategy that does not know $\ell$.

## Expansion

In a single jump-phase from $u$, the walk visits a node at distance $d$ with probability $\Theta(d^{-\alpha})$. For $\alpha\in(2,3)$ the jump length has finite mean but infinite variance, and the walk reaches distance $\ell$ in about $\ell^{\alpha-1}$ steps. The chance that it ever hits a given node at that distance is about $\ell^{\alpha-3}$, up to logarithmic factors. With $k$ independent walks, the success probability $1-(1-\ell^{\alpha-3})^k$ becomes large once $k\gtrsim\ell^{3-\alpha}$, which happens at $\alpha\approx3-\log k/\log\ell$. That exponent gives time $\ell^{\alpha-1}\approx\ell^2/k$. Smaller $\alpha$ makes each walk overshoot (fewer hits), and larger $\alpha$ makes it diffuse too slowly. So the optimum depends on both $k$ and $\ell$, in contrast to earlier single-searcher results where $\alpha=2$ is optimal. Drawing the exponent uniformly from $(2,3)$ puts about $(1/\log\ell)\cdot k$ walks within $O(1/\log\ell)$ of the optimal exponent for every distance at once, which costs only polylogarithmic factors. Animal groups searching independently from a nest, such as non-pheromone-marking desert ants, could therefore improve search efficiency either by tuning the exponent to the group size or by varying exponents across individuals.

## Sources

- Andrea Clementi, Francesco d'Amore, George Giakkoupis and Emanuele Natale, "Search via Parallel Lévy Walks on $\mathbb{Z}^2$", Proceedings of the 2021 ACM Symposium on Principles of Distributed Computing (2021), 81–91, <https://doi.org/10.1145/3465084.3467921>; numbering as in arXiv:2004.01562: Theorems 1.1, 1.2 and 1.3, Corollary 1.4, Theorem 1.5 and Theorem 1.6 (Section 1), with Definitions of Lévy flight and Lévy walk and the jump-phase visit corollary in Section 3 (Preliminaries); refined statements in Sections 4–6 and the algorithm analysis in Section 7.
