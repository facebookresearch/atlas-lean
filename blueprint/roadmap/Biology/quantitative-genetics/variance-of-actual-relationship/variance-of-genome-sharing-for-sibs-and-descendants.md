# Variance of genome sharing for half-sibs, full sibs and their descendants

With $\varphi_n$ as for [lineal relatives](genome-wide-variance-of-ibd-sharing-for-lineal-relatives.md), and Haldane's map function, suppose the expected two-locus sharing probability is a polynomial in $b=\tfrac12(1-c)$, $E(\breve k_{1i}\breve k_{1j})=\sum_na_nb^n$. Then the chromosome-wide variance of the shared proportion is

$$\operatorname{Var}(\breve k_1,l)=\sum_na_n\,\varphi_n(l).$$

For half sibs, $E(\breve k_{1i}\breve k_{1j})=\tfrac12(1-c)^2+\tfrac12c^2=4b^2-2b+\tfrac12$, so $\operatorname{Cov}(\breve k_{1i},\breve k_{1j})=\tfrac14(1-2c)^2$ and

$$\operatorname{Var}_{\mathrm{HS}}(\breve k_1,l)=4\varphi_2(l)-2\varphi_1(l),\qquad \operatorname{Var}_{\mathrm{HS}}(\breve R,l)=\varphi_2(l)-\tfrac12\varphi_1(l).$$

More generally, for relatives of relationship $(\tfrac12)^g$:

- half-sib descendants (half-uncle–nephew $g=3$, half cousins $g=4$): $\operatorname{Var}(\breve k_1,l)=4\varphi_g-2\varphi_{g-1}+\tfrac12\varphi_{g-2}$;
- uncle–nephew lines ($g=2$ uncle–nephew): $\operatorname{Var}(\breve k_1,l)=8\varphi_{g+1}-4\varphi_g+\tfrac12\varphi_{g-1}+\tfrac14\varphi_{g-2}$;
- cousins ($g=3$ first cousins, $g=5$ second cousins): $\operatorname{Var}(\breve k_1,l)=8\varphi_{g+1}-4\varphi_g+\tfrac32\varphi_{g-1}-\tfrac12\varphi_{g-2}+\tfrac18\varphi_{g-3}$;

and in each unilineal case $\operatorname{Var}(\breve R,l)=\tfrac14\operatorname{Var}(\breve k_1,l)$. For full sibs,

$$\operatorname{Var}_{\mathrm{FS}}(\breve R,l)=2\varphi_2(l)-\varphi_1(l),\qquad \operatorname{Var}_{\mathrm{FS}}(\breve k_2,l)=\operatorname{Var}_{\mathrm{FS}}(\breve k_0,l)=16\varphi_4-16\varphi_3+8\varphi_2-2\varphi_1 .$$

## Depends on

- [Genome-wide variance of IBD sharing for lineal relatives](genome-wide-variance-of-ibd-sharing-for-lineal-relatives.md)

## Expansion

Half sibs share at both loci when they receive the same non-recombinant or the same recombinant haplotype from the common parent. Writing $c=1-2b$ and expanding powers of $c$ turns any such probability into a polynomial in $b$. Under Haldane's map $b=\tfrac14(1+e^{-2(x-y)})$, and for unlinked loci $b=\tfrac14$, so subtracting the product of means gives $\sum_na_n(\tfrac14)^n[(1+e^{-2(x-y)})^n-1]$, whose average over $[0,l]^2$ is $\sum_na_n\varphi_n(l)$. Each further generation of descent multiplies the two-locus probability by $b$, which shifts indices. Full sibs combine two independent parental transmissions, giving higher powers.

## Sources

- W. G. Hill, B. S. Weir, "Variation in actual relationship as a consequence of Mendelian sampling and linkage", Genet. Res. 93 (2011), Sections 2(iii)–(iv), Equations (6)–(11) and Box 1, <https://doi.org/10.1017/S0016672310000480>, PMCID PMC3070763.
