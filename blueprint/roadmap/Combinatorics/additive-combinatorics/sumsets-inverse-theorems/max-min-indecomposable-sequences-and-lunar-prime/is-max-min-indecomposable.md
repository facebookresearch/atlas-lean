# Max-min indecomposable sequences

The predicate `IsMaxMinIndecomposable` records the factorization condition: for all sequences
$g, h : \mathbb{N} \to \mathbb{N}$ with $g \otimes h = f$, where $\otimes$ is the max-min product,
$g$ or $h$ is a monomial, that is, a sequence with exactly one nonzero term. The paper's
Definition 5 additionally excludes monomials; this predicate does not include that exclusion.

Factors range over all sequences $\mathbb{N} \to \mathbb{N}$; for $b \ge 2$ and $f$ with all terms
less than $b$, the coefficients can be restricted to $\{0, \dots, b - 1\}$ by applying the digit map
$x \mapsto \min(x, b - 1)$.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Definition 5.
