# A viability matrix negative definite on the simplex directions gives a unique, locally stable multiallelic polymorphism

Let $W$ be a symmetric matrix of positive genotype viabilities on $n$ alleles, with diploid selection map
$p'_i = p_i (Wp)_i / \bar w(p)$, $\bar w(p) = p^\top W p$, and suppose there is an interior equilibrium $p^*$: $p^*_i > 0$, $\sum_i p^*_i = 1$,
$W p^* = c\,\mathbf 1$. If $v^\top W v < 0$ for every nonzero $v$ with $\sum_i v_i = 0$, then $\bar w$ is strictly concave on the simplex and

$$\bar w(p) - \bar w(p^*) = (p - p^*)^\top W (p - p^*) < 0 \qquad (p \ne p^*),$$

so $p^*$ is the unique maximizer of mean fitness and the only interior equilibrium. Since mean fitness increases
strictly along every non-equilibrium trajectory, by the
[Baum–Eagon inequality](two-mul-rel-entropy-le-log-diploid-mean.md), and $p^*$ is a strict maximum, $p^*$ is
locally asymptotically stable. At any boundary equilibrium $q$ some allele absent from $q$ has marginal fitness
$(Wq)_i > \bar w(q)$, since $\sum_i p^*_i (Wq)_i = (Wp^*)^\top q = c > \bar w(q)$ while $(Wq)_i = \bar w(q)$ on the support of $q$; so that allele
increases when rare and no boundary equilibrium is stable. Boundary faces are invariant.

## Expansion

A sound expansion proves that every trajectory started in the interior converges to $p^*$ (a classical result
attributed to Kingman), and states the converse, that an interior equilibrium is unstable when the quadratic form is
not negative on the tangent space, with its own page.

## Depends on

- [Diploid Baum–Eagon mean-fitness inequality, sharp form](two-mul-rel-entropy-le-log-diploid-mean.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section II.9 (with multiple alleles mean fitness never decreases; stable equilibria are the maxima of mean fitness, with Kimura's and Kingman's conditions for alleles present and absent).
