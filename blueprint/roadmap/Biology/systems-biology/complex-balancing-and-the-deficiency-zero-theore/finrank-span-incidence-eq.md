# Rank of the reaction graph: number of complexes minus linkage classes

Let $K$ and $\rho$ be finite sets and $\sigma, \tau \colon \rho \to K$; in the reaction-network
reading, $K$ indexes the complexes and reaction $r$ goes from complex $\sigma(r)$ to complex
$\tau(r)$. Let $G$ be the simple graph on $K$ in which distinct $c, c' \in K$ are adjacent exactly
when some $r \in \rho$ has $\sigma(r) = c$ and $\tau(r) = c'$, or $\sigma(r) = c'$ and
$\tau(r) = c$, and let $\ell$ be the number of connected components of $G$ (the linkage classes).
With $(e_c)_{c \in K}$ the standard basis of $\mathbb{R}^K$, the incidence vectors
$e_{\tau(r)} - e_{\sigma(r)}$ of the reactions satisfy

$$\dim \operatorname{span} \{ e_{\tau(r)} - e_{\sigma(r)} : r \in \rho \} = |K| - \ell.$$

The right side is a difference of natural numbers, never truncated since $\ell \le |K|$. A reaction
with $\sigma(r) = \tau(r)$ contributes the zero vector and no edge. The proof identifies the vectors
of $\mathbb{R}^K$ orthogonal to this span with the kernel of the Laplacian of $G$, whose dimension
is $\ell$.

## Sources

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), § 6.4.
