# Remaining path partition after removing a minimum decycling set

**Setting.** Let $D_k$ be [Mykkeltveit's minimum decycling set](mykkeltveit-minimum-decycling-set-and-its-linear-time-membership-test.md) of the complete de Bruijn graph of order $k$, with the embedding $I(x) = \sum_{i} x_i \sin(2\pi i/k)$. A *remaining path* is a path in the graph after deleting the nodes of $D_k$.

**Theorem.** In every remaining path, all positive nodes ($I > 0$) precede all non-positive nodes ($I \le 0$): the path consists of a positive part followed by a non-positive part. Symmetrically, after removing the set $\tilde D_k$ defined by the first negative rotations, negative nodes precede all others in any remaining path.

**Consequence (minimizer orders).** A minimizer order compatible with the partition $\{D_k, \Sigma^k \setminus D_k\}$ (members of $D_k$ ranked first, random order within each class) selects a $k$-mer from $D_k$ in every window containing one. Using the *double decycling set* $D_k \cup \tilde D_k$ with partition $\{D_k, \tilde D_k \setminus D_k, \Sigma^k \setminus (D_k \cup \tilde D_k)\}$ leaves even shorter remaining paths, since no remaining path can contain both positive and negative $k$-mers; empirically these orders reach lower density than random and universal-hitting-set orders for large $k$.

## Depends on

- [Mykkeltveit minimum decycling set and its linear-time membership test](mykkeltveit-minimum-decycling-set-and-its-linear-time-membership-test.md)

## Expansion

Two lemmas drive the proof: all in-neighbours of a node $x$ have the same embedding value $I$ (they differ only in $y_0$, whose weight $\sin 0$ vanishes), and pure cycles partition the nodes. If a positive node $x_j$ followed a non-positive node on a remaining path, its predecessor on the path would share $I$ with its predecessor on its own pure cycle, making $x_j$ the first positive rotation of that cycle and hence a member of $D_k$, a contradiction.

## Sources

- D. Pellow, L. Pu, B. Ekim, L. Kotlar, B. Berger, R. Shamir and Y. Orenstein, "Efficient minimizer orders for large values of k using minimum decycling sets", *Genome Research* (2023), Methods, Theorem 1 (remaining path partition) with Lemmas 1–2, and the double decycling set construction. <https://doi.org/10.1101/gr.277644.123> (PMC10538483)
