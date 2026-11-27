# First-order modal logics of (ℕ, ≤) and (ℕ, <) are Π¹₁-hard with two variables

The first-order modal logics of the natural numbers with $\leq$ or $<$, with expanding or constant domains, are $\Pi^1_1$-hard and therefore not recursively enumerable, already for formulas with two individual variables, one monadic predicate letter and one proposition letter.

**Theorem (Rybakov and Shkatov).** Consider [first-order modal logics of single frames](first-order-modal-logics-of-linear-frames.md) in the language with two individual variables, one monadic predicate letter and one proposition letter.

1. Let $R$ be a binary relation on $\mathbb{N}$ with $< \;\subseteq R \subseteq\; \leq$, and let $L$ be a logic with $\mathbf{L}(\mathbb{N}, R) \subseteq L \subseteq \mathbf{L}_c(\mathbb{N}, R)$. Then satisfiability for $L$ is $\Sigma^1_1$-hard (Theorem 4.2); in particular this holds for $\mathbf{L}(\mathbb{N}, \leq)$ (Theorem 3.4) and for $\mathbf{L}_c(\mathbb{N}, \leq)$, $\mathbf{L}(\mathbb{N}, <)$ and $\mathbf{L}_c(\mathbb{N}, <)$ (Corollary 4.3).
2. Let $\alpha = \omega \cdot m + k$ with $1 \leq m < \omega$ and $k < \omega$, and let $R$ be a relation on $\alpha$ between $<$ and $\leq$. Then satisfiability for $\mathbf{L}(\alpha, R)$ is $\Sigma^1_1$-hard (Theorem 4.4).

Since $\varphi$ is satisfiable exactly when $\neg\varphi \notin L$, each such logic is $\Pi^1_1$-hard, hence not recursively enumerable.

## Depends on

- [First-order modal logics of single Kripke frames](first-order-modal-logics-of-linear-frames.md)

## Proof depends on

None.

## Expansion

The proof encodes the recurrent $\mathbb{N} \times \mathbb{N}$ tiling problem, which is $\Sigma^1_1$-complete (Harel, Theorem 6.4, as quoted in the source): given a finite set of tile types and a designated type, is there a tiling of the quadrant in which the designated type occurs infinitely often in the leftmost column? For each tile set a formula in the restricted language is built that is satisfiable over $(\mathbb{N}, R)$ exactly when a recurrent tiling exists; the order type of $\mathbb{N}$ is what allows the recurrence condition to be expressed. A good expansion links a page for the $\Sigma^1_1$-completeness of the recurrent tiling problem, which has none yet.

## Sources

- M. Rybakov and D. Shkatov, "Algorithmic properties of first-order modal logics of linear Kripke frames in restricted languages", *Journal of Logic and Computation* 31(5):1266–1288, 2021, doi:10.1093/logcom/exab030; read as arXiv:2105.11811v1, <https://arxiv.org/abs/2105.11811v1>, whose numbering is used here: Theorems 3.4, 4.2 and 4.4, Corollary 4.3, and Sections 3 and 4.
