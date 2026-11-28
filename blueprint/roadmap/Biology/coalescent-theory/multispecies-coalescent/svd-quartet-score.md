# SVD quartet score

Let $\hat P$ be the empirical site-pattern distribution of four taxa from $M$ unlinked sites, and for each of the three splits $L_1 \mid L_2$ of the quartet into pairs let $\hat\sigma_1 \ge \dots \ge \hat\sigma_{16} \ge 0$ be the singular values of the $16 \times 16$ flattening $\mathrm{Flat}_{L_1 \mid L_2}(\hat P)$. The *SVD score* of the split is

$$\mathrm{SVD}(L_1 \mid L_2) = \sum_{i=11}^{16} \hat\sigma_i^2 = \min_{\operatorname{rank} B \le 10} \bigl\|\mathrm{Flat}_{L_1 \mid L_2}(\hat P) - B\bigr\|_F^2, \tag{2}$$

the squared Frobenius distance to the nearest matrix of rank at most $10$ (Eckart–Young). The estimated quartet is the split with the smallest score; bootstrap resampling of sites gives split support.


## Depends on

- [Flattening rank under the multispecies coalescent](flattening-rank-under-the-multispecies-coalescent.md)

## Expansion

**Derived remark (statistical consistency).** For independent sites drawn from $P$ under the multispecies coalescent with a GTR model at generic parameters, $\hat P \to P$ almost surely by the strong law of large numbers, and singular values are continuous functions of the matrix (Weyl's inequality), so each score converges to $\sum_{i \ge 11} \sigma_i(\mathrm{Flat}(P))^2$. This limit is $0$ for the valid split, whose flattening has rank at most $10$, and positive for a non-valid split at generic parameters, whose flattening has rank above $10$. The identity in (2) is the Eckart–Young theorem with $\|A\|_F^2 = \sum_i \sigma_i^2$.

## Sources

- J. Chifman and L. Kubatko, *Quartet inference from SNP data under the coalescent model*, Bioinformatics 30 (2014), 3317–3324, <https://doi.org/10.1093/bioinformatics/btu530>, PMCID PMC4296144 (Section 2.1, equation (2)).
