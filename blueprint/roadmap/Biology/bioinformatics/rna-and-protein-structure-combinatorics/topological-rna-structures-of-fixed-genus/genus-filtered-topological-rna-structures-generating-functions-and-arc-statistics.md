# Genus-filtered topological RNA structures: generating functions and arc statistics

**Setting.** An RNA contact structure on $n$ nucleotides is a linear chord diagram: the backbone is a horizontal line of $n$ vertices, and base pairs are noncrossing or crossing arcs. Collapsing each vertex sequence to a polygon and arcs to ribbons gives a fatgraph, whose topological **genus** $g$ filters structures: secondary structures are exactly the genus-$0$ structures, and pseudoknots need $g \ge 1$. Biologically, structures are restricted to **minimum arc-length** $\lambda$ (each arc $(i,j)$ has $j - i \ge \lambda$) and **minimum stack-length** $r$ (every maximal run of parallel arcs has length at least $r$). Let $\mathbf{D}_g(x,y) = \sum d_g(n,l)\,x^ny^l$ count such structures of genus $g$ by length $n$ and number of arcs $l$.

**Background.** Linear chord diagrams of genus $g \ge 1$ with $n$ chords have generating function $\mathbf{C}_g(x) = \sum_{n=2g}^{3g-1}\kappa_g(n)\,x^n/(1-4x)^{n+1/2}$, and **shapes** (linear chord diagrams without $1$-arcs $(i,i+1)$ in which every stack has length one) of genus $g$ have generating polynomial $\mathbf{S}_g(x) = \sum_{n=2g}^{3g-1}\kappa_g(n)\,x^n(1+x)^{n+1}$, with the same positive integers $\kappa_g(n)$. For genus $0$,

$$ \mathbf{D}_0 = \frac{\mathbf{B} - \sqrt{\mathbf{B}^2 - 4(x^2y)^r\mathbf{A}}}{2(x^2y)^r}, \qquad \mathbf{A} = 1 - x^2y + (x^2y)^r, \quad \mathbf{B} = (1-x)\mathbf{A} + (x^2y)^r\sum_{i=0}^{\lambda-2}x^i . $$

**Theorem.** Let $g, \lambda, r \ge 1$ with $\lambda \le r + 1$.

*(1)* (Shape decomposition)

$$ \mathbf{D}_g(x,y) = \mathbf{D}_0(x,y)\,\mathbf{S}_g\!\left(\frac{(x^2y)^r\mathbf{D}_0(x,y)^2}{1 - x^2y - (x^2y)^r\big(\mathbf{D}_0(x,y)^2 - 1\big)}\right) = \frac{\mathbf{A}}{\mathbf{B}}\,\mathbf{C}_g\!\left(\frac{(x^2y)^r\mathbf{A}}{\mathbf{B}^2}\right). $$

*(2)* (Singular expansion) As $x \to \rho(y)$, uniformly for $y$ near $1$, $\mathbf{D}_g(x,y) = \delta_g(y)(\rho(y) - x)^{-(6g-1)/2}(1 + o(1))$, where $\rho(y)$ is the minimal positive root of $\mathbf{B}^2 - 4(x^2y)^r\mathbf{A} = 0$ (the same singularity as for secondary structures) and $\delta_g(1) \ne 0$. Hence

$$ [x^n]\,\mathbf{D}_g(x,y) = c_g(y)\,n^{(6g-3)/2}\rho(y)^{-n}\big(1 + O(n^{-1})\big). $$

*(3)* (Central limit theorem) The number of arcs $\mathbb{Y}_{g,n}$ of a uniformly random genus-$g$ structure of length $n$ satisfies

$$ \frac{\mathbb{Y}_{g,n} - \mu n}{\sqrt{n\sigma^2}} \Rightarrow \mathcal{N}(0,1) \quad \text{with speed } O(n^{-1/2}), \qquad \mu = -\frac{\theta'(0)}{\theta(0)},\quad \sigma^2 = \Big(\frac{\theta'(0)}{\theta(0)}\Big)^2 - \frac{\theta''(0)}{\theta(0)},\quad \theta(s) = \rho(e^s). $$

The same shape-substitution scheme gives generating functions, singular expansions and Gaussian limits for stacks, hairpin loops, interior loops and multiloops. The expected numbers of H-type pseudoknots, kissing hairpins and 3-knots follow from the irreducible shadows of genus $1$.

## Expansion

Every genus-$g$ structure arises uniquely from a shape of genus $g$ by inflating each arc into a stack of parallel arcs (with at least $r$ arcs, separated by genus-$0$ insertions) and each gap into a secondary structure. This substitution turns $\mathbf{S}_g$ into $\mathbf{D}_g$, and the second form $\frac{\mathbf{A}}{\mathbf{B}}\mathbf{C}_g(z)$ with $z = (x^2y)^r\mathbf{A}/\mathbf{B}^2$ explains the singularity: $1 - 4z = (\mathbf{B}^2 - 4(x^2y)^r\mathbf{A})/\mathbf{B}^2$ vanishes linearly at $x = \rho(y)$, and the most singular term of $\mathbf{C}_g$, $(1-4z)^{-(3g-1)-1/2}$, gives the exponent $-(6g-1)/2$. The singularity $\rho(y)$ is independent of $g$ and analytic in $y$, so the quasi-power theorem gives the Gaussian law for arcs, with mean and variance read off from $\rho(e^s)$.

## Sources

- Thomas J. X. Li and Christian M. Reidys, "Statistics of topological RNA structures", arXiv:1606.06956 (2016), Section 2 (basic facts, genus-0 generating function), Section 3 (shape decomposition and singular expansion of $\mathbf{D}_g$), Section 4 (central limit theorem for arcs), Sections 5–7 (loops, block decomposition, irreducible shadows), <https://doi.org/10.48550/arXiv.1606.06956>.
