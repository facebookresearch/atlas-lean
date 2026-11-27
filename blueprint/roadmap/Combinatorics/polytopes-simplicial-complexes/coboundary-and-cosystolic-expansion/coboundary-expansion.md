# Coboundary expansion of a simplicial complex

Let $X$ be a pure $d$-dimensional weighted complex and $0 \le i < d$, with cochains, coboundaries and weighted norms taken in the augmented cochain complex ($X(-1) = \{\emptyset\}$, with $\delta_{-1}$ mapping onto the constant $0$-cochains), so that $B^0$ consists of the two constant $0$-cochains. The **$i$-th coboundary expansion** of $X$ over $\mathbb{F}_2$ is

$$
h^i(X) = \min_{f \in C^i \setminus B^i} \frac{\|\delta_i f\|}{\operatorname{dist}(f, B^i)}, \qquad \operatorname{dist}(f, B^i) = \min_{g \in B^i} \|f - g\|.
$$

$X$ is an **$\varepsilon$-coboundary expander** in dimension $i$ if $h^i(X) \ge \varepsilon$. A positive $h^i(X)$ forces $H^i(X; \mathbb{F}_2) = 0$, since a cocycle outside $B^i$ would give the ratio $0$; for $i = 0$ this is the reduced cohomology, so $h^0(X) > 0$ forces the $1$-skeleton to be connected. For $i = 0$, a cochain $f \notin B^0$ is the indicator of a set $S$ with $\emptyset \ne S \subsetneq X(0)$, $\|\delta_0 f\|$ is the $\Pi_1$-measure of the edges between $S$ and its complement, and $\operatorname{dist}(f, B^0) = \min(\Pi_0(S), \Pi_0(X(0) \setminus S))$; so

$$
h^0(X) = \min_{\emptyset \ne S \subsetneq X(0)} \frac{\Pi_1\bigl(E(S, X(0) \setminus S)\bigr)}{\min\bigl(\Pi_0(S), \Pi_0(X(0) \setminus S)\bigr)},
$$

the normalized edge expansion (Cheeger constant) of the weighted $1$-skeleton.

## Depends on

- [Cochains and the coboundary operator over F_2](cochains-coboundary.md)

## Sources

- N. Linial, R. Meshulam, "Homological connectivity of random 2-complexes", Combinatorica 26 (2006) 475-487.
- M. Gromov, "Singularities, expanders and topology of maps. Part 2: from combinatorics to topology via algebraic isoperimetry", Geometric and Functional Analysis 20 (2010) 416-526.
- A. Lubotzky, "High dimensional expanders", Proceedings of the ICM (2018), arXiv:1712.02526.
