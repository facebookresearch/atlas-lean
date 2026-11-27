# Order of the general linear group over a finite field

Let $\mathbb{F}$ be a finite field with $q$ elements and let $n \ge 0$. Then the group $\mathrm{GL}_n(\mathbb{F})$ of
invertible $n \times n$ matrices over $\mathbb{F}$ has order

$$\# \mathrm{GL}_n(\mathbb{F}) = \prod_{i=0}^{n-1} (q^n - q^i).$$

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>, Section 4.2,
  the table of dimensions and numbers of points after Lemma 4.2.5 (p. 53): $\# \mathrm{GL}_m(\mathbb{F}_q) = q^{m(m-1)/2} \prod_{j=1}^m (q^j - 1)$,
  the same number, since $q^n - q^i = q^i (q^{n-i} - 1)$.
