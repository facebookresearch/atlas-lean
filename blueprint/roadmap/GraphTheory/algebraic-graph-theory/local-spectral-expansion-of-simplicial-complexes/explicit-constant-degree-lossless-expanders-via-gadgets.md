# Golowich: explicit constant-degree lossless expanders via gadget products

A bipartite graph $G$ with left vertex set $L(G)$, right vertex set $R(G)$ and left degree $D$ is a (one-sided) $(\mu, \varepsilon)$-lossless expander if every $S \subseteq L(G)$ with $|S| \le \mu |L(G)|$ has at least $(1 - \varepsilon) D |S|$ neighbours. For every open interval $(\beta_1, \beta_2) \subseteq (0, \infty)$ and every $\varepsilon > 0$ there are $D = D(\beta_1, \beta_2, \varepsilon) \in \mathbb{N}$, $\mu = \mu(\beta_1, \beta_2, \varepsilon) > 0$ and an infinite explicit family of $(\mu, \varepsilon)$-lossless expanders with left degree $D$ whose size ratios satisfy $|R(G)|/|L(G)| \in (\beta_1, \beta_2)$. The ratio is prescribed only up to such an interval: it is a rational number for every finite graph.

## Proof sketch

Start from a large $(k, D_0)$-biregular bipartite graph $X$ whose non-lazy square on the right is a good spectral expander, and a constant-size $(\mu_0, \varepsilon_0)$-lossless expander $G_0$ with $D_0$ left vertices and left degree $d_0$. Set $L(G) = L(X)$ and $R(G) = R(X) \times R(G_0)$, and for every $v \in R(X)$ place a copy of $G_0$ between the neighbourhood $N_X(v)$ and $\{v\} \times R(G_0)$; the left degree is $D = k d_0$. The right sides of different gadgets are disjoint, so the neighbourhood of $S$ is the disjoint union of its neighbourhoods inside the gadgets, and nothing collides across gadgets. Call $v \in R(X)$ heavy if $|N_X(v) \cap S| \ge \mu_0 D_0$; inside a non-heavy gadget, $N_X(v) \cap S$ expands losslessly by $(1 - \varepsilon_0) d_0$. The expander mixing lemma for the square of $X$ bounds the incidences between $S$ and heavy vertices: all but a $1/(5k)$ fraction of $S$ is adjacent to at most one heavy vertex, hence to at least $k - 1$ non-heavy gadgets, and summing gives $(1 - \varepsilon) D |S|$ neighbours for suitable parameters.

## Depends on

- [Uniform vertex expander](../../graph-families-and-operations/expander-graphs/is-uniform-vertex-expander.md)

## Proof depends on

- [Expander mixing lemma](../../graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)

## Sources

- Louis Golowich, "New explicit constant-degree lossless expanders", SODA (2024); arXiv:2306.07551 (Definition 1, Theorem 2, Proposition 16).
- Michael Capalbo, Omer Reingold, Salil Vadhan, Avi Wigderson, "Randomness conductors and constant-degree lossless expanders", STOC (2002).
