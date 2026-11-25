# Principal minors of the Fourier matrix

Let $M \ge 2$, let $R$ be a commutative ring, let $\zeta \in R$ be a primitive $M$-th root of unity, and let $S$ be a finite subset of $\mathbb{Z}/M\mathbb{Z}$. The principal Fourier minor indexed by $S$ is the $S \times S$ matrix over $R$ whose $(i, j)$ entry is $\zeta^n$, where $n \in \{0, \dots, M - 1\}$ represents the product $ij$ in $\mathbb{Z}/M\mathbb{Z}$.

## Idea

The Fourier matrix of order $M$ has entries $\zeta^{ij}$; choosing the same set $S$ of rows and columns gives a principal submatrix. When are its determinants nonzero? Chebotarev's theorem says that for $M$ prime and $\zeta = e^{2\pi i/M}$ every square submatrix of the Fourier matrix is invertible, a fact behind uncertainty principles for the discrete Fourier transform and compressed sensing. For other $M$ some principal minors can vanish: if $a^2$ divides $M$ with $a > 1$, the minor indexed by $\{0, M/a\}$ is $\zeta^{(M/a)^2} - 1 = 0$. Describing which principal minors vanish is a research question. The basic facts here fix the conventions: the empty minor has determinant $1$ and a singleton $\{a\}$ gives $\zeta^{a^2}$.

## Statements

- [Principal Fourier minor](principal-minor-matrix.md)
- [Determinant of a principal Fourier minor](principal-minor-det.md): its determinant
- [Entries of a principal Fourier minor](principal-minor-matrix-apply.md): its entries
- [Determinant of the empty principal Fourier minor](principal-minor-det-empty.md): the empty minor has determinant $1$
- [Determinant of a singleton principal Fourier minor](principal-minor-det-singleton.md): a singleton minor
- [Primitive root of unity data](root-data.md): the root-of-unity data
