# Accessibility percolation equals first-passage site percolation

**Setting.** Let $G = (V, E)$ be a finite or locally finite graph whose edges may be directed or undirected, with a distinguished vertex $\mathbf 0$. A *fitness landscape* $\omega : V \to \mathbb R$ makes a path $v_0 \to v_1 \to \dots \to v_l$ *accessible* if $\omega(v_0) < \omega(v_1) < \dots < \omega(v_l)$, and $w$ is accessible from $v$ if some accessible path joins them. In the *House-of-Cards* model the $\omega(v)$ are independent $U(0,1)$; in the variant with an *a priori global maximum* $\mathbf v$, $\omega(\mathbf v)$ is set to $1$. Write $\mathbb P^\alpha$ for probabilities conditional on $\omega(\mathbf 0) = \alpha$.

Independently assign each vertex a cost $c(v) \sim U(0,1)$. For a path $u_0, u_1, \dots, u_l$ the *site passage time* is $\sum_{1 \le i \le l} c(u_i)$ and the *reduced site passage time* is $\sum_{1 \le i < l} c(u_i)$ (neither counts the first vertex; the reduced one also omits the last). Let $\mathcal T_V(u,v)$ and $\mathcal T'_V(u,v)$ be the minima of these over all paths from $u$ to $v$.

**Theorem.** Let $\alpha \in [0,1]$.

1. With an a priori global maximum at $\mathbf v \neq \mathbf 0$,

$$ \mathbb P^\alpha(\mathbf v \text{ accessible from } \mathbf 0) = \mathbb P\big(\mathcal T'_V(\mathbf 0, \mathbf v) \le 1 - \alpha\big). $$

2. Without an a priori maximum, for every vertex $v$,

$$ \mathbb P^\alpha(v \text{ accessible from } \mathbf 0) = \mathbb P\big(\mathcal T_V(\mathbf 0, v) \le 1 - \alpha\big), $$

   and more strongly, given $\omega(\mathbf 0) = \alpha$, the random set of vertices accessible from $\mathbf 0$ has the same law as $\{v : \mathcal T_V(\mathbf 0, v) \le 1 - \alpha\}$.

The equivalence concerns which vertices are reachable, not the number of accessible paths, which can differ even on directed acyclic graphs. If the vertex costs are replaced by independent $U(0,1)$ edge weights with first-passage time $\mathcal T_E$, the two can be coupled so that $\mathcal T_E(\mathbf 0, v) \le \mathcal T_V(\mathbf 0, v)$ for all $v$.

## Expansion

First-passage times can be computed by a Dijkstra-type exploration: repeatedly pick the explored vertex $u$ of least passage time with an unexplored neighbour $v$ and set $\mathcal T_V(\mathbf 0, v) = \mathcal T_V(\mathbf 0, u) + c(v)$; each cost is read once, so the costs read form an i.i.d. $U(0,1)$ sequence. The coupling sets the fitness to $f(v) = \{\alpha + \mathcal T_V(\mathbf 0, v)\}$ (fractional part). Generating each cost at the moment it is read as $c(v) = \{\tilde f(v) - \alpha - \mathcal T_V(\mathbf 0, u)\}$ from a fresh uniform $\tilde f(v)$ shows that $f = \tilde f$, so the $f(v)$, $v \ne \mathbf 0$, are independent uniforms: $f$ is a House-of-Cards landscape with $f(\mathbf 0) = \alpha$. If $\mathcal T_V(\mathbf 0, v) \le 1 - \alpha$, along a cheapest path $f(v_i) = \alpha + \sum_{j \le i} c(v_j)$ increases, so the path is accessible; if $\mathcal T_V(\mathbf 0, v) > 1 - \alpha$, every path has a first vertex whose passage time exceeds $1 - \alpha$, where the fractional part wraps around and the fitness drops, so no path is accessible. With an a priori maximum at $\mathbf v$, accessibility of $\mathbf v$ is equivalent to accessibility of one of its in-neighbours, i.e. to $\min_{u \to \mathbf v}\mathcal T_V(\mathbf 0, u) = \mathcal T'_V(\mathbf 0, \mathbf v) \le 1 - \alpha$. Running the same exploration with edge weights instead of vertex costs produces the coupling with bond percolation. The identity transfers results between the two literatures, in particular for accessibility percolation on trees.

## Sources

- Anders Martinsson, "Accessibility percolation and first-passage site percolation on the unoriented binary hypercube", arXiv:1501.02206 (2015), Section 1 (Definition of accessibility, House-of-Cards models, Theorem 1.4, Proposition 1.5), Section 2 (proof of Proposition 1.5 and Theorem 1.4, Lemma 2.1). <https://doi.org/10.48550/arXiv.1501.02206>
