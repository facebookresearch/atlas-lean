# Ligation advantage of compositionally diverse templates

Consider a template offering $N\ge1$ candidate ligation sites. Let $p_1\in(0,1)$ be the probability that a pair of substrate fragments anneals adjacently at a site and $p_2\in(0,1)$ the probability that a bond then forms. Compare a compositionally diverse (high $C_k$) template, whose $N$ sites are distinct and anneal independently, with a repetitive (low $C_k$) template, whose sites are copies of one motif so that annealing happens to all sites or none. The probabilities that at least one ligation occurs are

$$p_{\mathrm{high}}=1-(1-p_1p_2)^N,\qquad p_{\mathrm{low}}=p_1\bigl[1-(1-p_2)^N\bigr],$$

and their ratio

$$R=\frac{p_{\mathrm{high}}}{p_{\mathrm{low}}}=\frac{1-(1-p_1p_2)^N}{p_1\bigl[1-(1-p_2)^N\bigr]}$$

satisfies $R\ge1$, with equality if and only if $N=1$.

## Depends on

- [Relative k-mer compositional diversity of a sequence](relative-k-mer-compositional-diversity.md)

## Expansion

Fix $p_2$ and set $g(t)=1-(1-tp_2)^N$ for $t\in[0,1]$. Then $g(0)=0$ and $g''(t)=-N(N-1)p_2^2(1-tp_2)^{N-2}$, so $g$ is concave, strictly when $N\ge2$. Concavity with $g(0)=0$ gives $g(p_1)\ge p_1\,g(1)$, strictly for $0<p_1<1$ when $N\ge2$, which is $p_{\mathrm{high}}\ge p_{\mathrm{low}}$. For $N=1$ both probabilities are $p_1p_2$. The source states the ratio and the conclusion $R>1$, deferring the derivation to its supplementary data; the reading of $N$ as the number of sites and the concavity proof are given here. The consequence drawn in the source is that internally diverse sequences are better templates and so propagate their sequence information preferentially, which it tested with binary DNA templates of varying $C_3$.

## Sources

- J. Derr, M. L. Manapat, S. Rajamani, K. Leu, R. Xulvi-Brunet, I. Joseph, M. A. Nowak and I. A. Chen, "Prebiotically plausible mechanisms increase compositional diversity of nucleic acid sequences", Nucleic Acids Research 40 (2012), 4711–4722, Results ("Experimental: compositional diversity in template-directed ligation of DNA"), <https://doi.org/10.1093/nar/gks065> (PMC3378899).
