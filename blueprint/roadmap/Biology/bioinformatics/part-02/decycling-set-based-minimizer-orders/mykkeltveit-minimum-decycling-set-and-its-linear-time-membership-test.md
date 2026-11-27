# Mykkeltveit minimum decycling set and its linear-time membership test

**Setting.** Let $\Sigma = \{0, 1, \dots, \sigma - 1\}$ (for DNA, $A = 0, C = 1, G = 2, T = 3$) and consider the complete de Bruijn graph of order $k$, whose nodes are all $k$-mers $x = x_0 x_1 \cdots x_{k-1}$ and whose arcs join $x$ to every $x_1 \cdots x_{k-1} a$. A *decycling set* is a set of nodes meeting every cycle; one of minimum size is a minimum decycling set (MDS). A *pure cycle* is the set of cyclic rotations of a $k$-mer; pure cycles partition the nodes, so an MDS has at least one node per pure cycle. The *Mykkeltveit embedding* of $x$ is

$$M(x) = \bigl(R(x), I(x)\bigr) = \Bigl(\sum_{i=0}^{k-1} x_i \cos\tfrac{2\pi i}{k},\; \sum_{i=0}^{k-1} x_i \sin\tfrac{2\pi i}{k}\Bigr),$$

and $x$ is *positive* if $I(x) > 0$. Within each pure cycle the positive rotations are consecutive, and either all rotations have $I = 0$ or the positive and negative blocks are separated by at most one zero rotation on each side.

**Mykkeltveit's set.** $D_k$ contains, from each pure cycle, the first positive rotation in counterclockwise order, that is, the positive $x$ whose rotation $x' = x_{k-1} x_0 \cdots x_{k-2}$ has $I(x') \le 0$; from a pure cycle with all $I = 0$ it contains one representative (the lexicographically smallest rotation). Then $D_k$ is a minimum decycling set, with exactly one node per pure cycle.

**Proposition.** Membership $x \in D_k$ can be decided in $O(k)$ time and $O(1)$ extra memory: compute $I(x)$ and $I(x')$; return true if $I(x) > 0 \ge I(x')$; if $I(x) = I(x') = 0$, all rotations have zero embedding and $x$ is accepted iff it is the lexicographically smallest rotation, which a single $O(k)$ scan over the doubled string decides.

## Expansion

Because a pure cycle contributes exactly one node, $|D_k|$ equals the number of conjugacy classes (necklaces), the classical lower bound for a decycling set; Mykkeltveit proved that this choice hits every cycle, not only the pure ones. The membership test avoids storing $D_k$, whose size grows like $\sigma^k/k$, which is what allows decycling-based minimizer orders for $k$ in the hundreds.

## Sources

- D. Pellow, L. Pu, B. Ekim, L. Kotlar, B. Berger, R. Shamir and Y. Orenstein, "Efficient minimizer orders for large values of k using minimum decycling sets", *Genome Research* (2023), Methods (Mykkeltveit embedding, Figure 1, Algorithm 1) and Proposition 1, building on Mykkeltveit (1972), Lemma 1. <https://doi.org/10.1101/gr.277644.123> (PMC10538483)
