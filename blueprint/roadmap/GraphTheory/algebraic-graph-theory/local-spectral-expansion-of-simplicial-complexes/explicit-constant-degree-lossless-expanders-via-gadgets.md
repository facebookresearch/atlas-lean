# Golowich: explicit constant-degree lossless expanders via gadget products

For every $\varepsilon > 0$ and every constant ratio $\beta > 0$ there are explicit infinite families of one-sided bipartite graphs with left degree $D = O_{\varepsilon, \beta}(1)$ and right-to-left size ratio $\beta$ such that every left set $S$ of size at most $\gamma n$ has at least $(1 - \varepsilon)D|S|$ neighbours (lossless expansion), constructed by placing a constant-size lossless expander gadget inside the neighbourhoods of a large bipartite spectral expander.

## Proof sketch

Each left vertex's $D$ edges are distributed according to a gadget on its neighbourhood in a base spectral expander. Elementary counting shows that small sets either expand losslessly within gadgets or create many collisions, and collisions across gadgets are bounded by the expander mixing lemma of the base graph, giving $(1-\varepsilon)D|S|$ neighbours.

## Depends on

- [Expander mixing lemma](../../graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)
- [Uniform vertex expander](../../graph-families-and-operations/expander-graphs/is-uniform-vertex-expander.md)

## Proof depends on

- [Expander mixing lemma](../../graph-families-and-operations/expander-graphs/expander-mixing-lemma.md)
- [Uniform vertex expander](../../graph-families-and-operations/expander-graphs/is-uniform-vertex-expander.md)

## Sources

- Louis Golowich, "New explicit constant-degree lossless expanders", SODA (2024); arXiv:2306.07551.
- Michael Capalbo, Omer Reingold, Salil Vadhan, Avi Wigderson, "Randomness conductors and constant-degree lossless expanders", STOC (2002).
