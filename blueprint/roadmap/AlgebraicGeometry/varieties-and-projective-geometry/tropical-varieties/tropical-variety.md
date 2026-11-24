# Tropicalization of an ideal of Laurent polynomials

Let $K$ be a field with a valuation $\mathrm{val} : K \to \mathbb{R} \cup \{\infty\}$ and let $I$ be
an ideal of Laurent polynomials in $n$ variables over $K$. The tropicalization of $I$ is the
intersection $\operatorname{trop}(I) = \bigcap_{f \in I,\, f \neq 0} \operatorname{trop}(V(f))$ of
the tropical hypersurfaces of the nonzero polynomials in $I$ (Maclagan–Sturmfels, draft 2009,
Definition 3.2.1, equation (3.1), where it is written $\operatorname{trop}(X)$ for the variety
$X = V(I) \subseteq (K^*)^n$, $K$ being algebraically closed with a nontrivial valuation
throughout Chapter 3). It depends on $I$, not only on its set of zeros: for $K = \mathbb{R}$ with
the trivial valuation and $n = 1$, the ideals $(x^2 + 1)$ and $(1)$ both have no zeros in
$K^*$, but their tropicalizations are $\{0\}$ and $\emptyset$. The zero polynomial is left out of
the intersection: its tropical hypersurface is empty, and leaving it out makes the zero ideal
tropicalize to $\mathbb{R}^n$, as Theorem 3.2.4 requires; the source says nothing about $f = 0$.
