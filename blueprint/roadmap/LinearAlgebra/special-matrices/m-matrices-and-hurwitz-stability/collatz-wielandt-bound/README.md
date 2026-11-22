# Collatz–Wielandt lower bound

Let $K$ be a real square matrix, with rows and columns indexed by a finite set, whose entries are all
nonnegative. If $z$ is a nonzero vector with nonnegative entries and $r \ge 0$ is a real number with
$r z \le K z$ entrywise, then $r$ is at most the spectral radius of $K$, viewed as a complex matrix.

## Idea

A nonnegative test vector that $K$ stretches by at least $r$ in every coordinate certifies that the
spectral radius is at least $r$. Since $K$ preserves entrywise inequalities between nonnegative
vectors, $r z \le K z$ iterates to $r^j z \le K^j z$, so the norms of the powers $K^j$ grow at least like
$r^j$, and Gelfand's formula $\rho(K) = \lim_j \|K^j\|^{1/j}$ gives $\rho(K) \ge r$. Collatz and
Wielandt showed that, for a matrix with at least one row, the best such bound over all test vectors is the
spectral radius itself, attained by a nonnegative eigenvector.

## Statements

- [Collatz–Wielandt lower bound](le-spectral-radius-of-smul-le-mul-vec.md)
