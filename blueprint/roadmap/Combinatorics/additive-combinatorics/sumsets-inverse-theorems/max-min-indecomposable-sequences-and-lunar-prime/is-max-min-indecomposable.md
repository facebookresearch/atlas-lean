# Max-min indecomposable sequences

The predicate `IsMaxMinIndecomposable` records the factorization condition: for all sequences
$g, h : \mathbb{N} \to \mathbb{N}$ with $g \otimes h = f$, where $\otimes$ is the max-min product,
$g$ or $h$ is a monomial, that is, a sequence with exactly one nonzero term. The paper's
Definition 5 additionally excludes monomials; this predicate does not include that exclusion.

Factors here are arbitrary natural-valued sequences, and a monomial has exactly one nonzero
coefficient. Definition 5 uses finite base-$b$ polynomials and writes monomials as $t x^n$,
allowing $t = 0$. For a digit sequence with nonzero constant term, any factorization has
nonzero, finitely supported factors: a nonzero coefficient of either factor survives by pairing
with the other factor's nonzero constant term. For $b \ge 2$, clipping the factors at $b - 1$
preserves their supports, the max-min product clipped at $b - 1$, and thus the monomial condition.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Definition 5.
