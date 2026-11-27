# Top-degree coefficients are invariant under a translation of the marker coding

**Setting.** Let $M\in\mathbb R^{n\times p}$ be a marker matrix with rows $M_{i,\bullet}$ (one per individual) and let $P\in\mathbb R^{p}$ be any vector. The translated coding is

$$\tilde M := M-\mathbf 1_n P^{t},$$

so column $j$ is shifted by the constant $P_j$ (for example, $P$ the column means gives the centred coding, and $P=(1,\dots,1)$ turns $0/1/2$ into $-1/0/1$).

**Definition (complete polynomial model).** A polynomial model $f:\mathbb R^p\to\mathbb R$ in the marker values is *complete* if, for every monomial $M_{i,j_1}^{d_1}\cdots M_{i,j_m}^{d_m}$ that carries a free coefficient, every monomial $M_{i,j_1}^{\delta_1}\cdots M_{i,j_m}^{\delta_m}$ with $0\le\delta_k\le d_k$ also carries a free coefficient. The pairwise epistasis model

$$y_i=\mu+\sum_{k}\beta_k M_{i,k}+\sum_{k<l}h_{k,l}M_{i,k}M_{i,l}+\epsilon_i$$

is complete; the model $y_i=\mu+\beta_1M_{i,1}+h_{1,2}M_{i,1}M_{i,2}+\epsilon_i$ is not, because $M_{i,2}$ is missing.

**Proposition.** Let $f$ be a polynomial of total degree $D$ in the marker values and define the polynomial $\tilde f$ in the translated variables by

$$\tilde f(\tilde M_{i,\bullet}) := f(\tilde M_{i,\bullet}+P^{t}) = f(M_{i,\bullet}).$$

Then for any phenotype vector $y\in\mathbb R^n$,

$$\sum_{i=1}^n\bigl(y_i-f(M_{i,\bullet})\bigr)^2=\sum_{i=1}^n\bigl(y_i-\tilde f(\tilde M_{i,\bullet})\bigr)^2,$$

and for every monomial $m$ of the highest total degree $D$ the coefficients agree: $a_m=\tilde a_m$.

The top-degree coefficients are the additive effects in an additive model, the pairwise interaction effects in a model of total degree 2, the three-way interactions in degree 3, and so on. Coefficients of lower total degree generally change under the translation; in an incomplete model a coefficient forced to zero in $f$ may need to be nonzero in $\tilde f$, so the map $f\mapsto\tilde f$ need not stay inside the model.

## Expansion

Equality of the residual sums of squares holds by construction, since $\tilde f$ and $f$ take the same value at corresponding points. For a top-degree monomial $m(M_{l_1},\dots,M_{l_d})$, expanding $m(\tilde M_{l_1}+P_{l_1},\dots,\tilde M_{l_d}+P_{l_d})$ reproduces $m(\tilde M_{l_1},\dots,\tilde M_{l_d})$ as the only summand of total degree $D$; every other summand has lower degree and is absorbed into lower-order coefficients. Completeness is exactly what guarantees those lower-order coefficients are free parameters, so that $\tilde f$ belongs to the same model class.

## Sources

- J. W. R. Martini, F. Rosales, N.-T. Ha, J. Heise, V. Wimmer, T. Kneib, "Lost in Translation: On the Problem of Data Coding in Penalized Whole Genome Regression with Interactions", *G3: Genes, Genomes, Genetics* (2019), Proposition 1, Definition 1, Example 1, section "Translations of the marker coding", and the Appendix proof of Proposition 1, <https://doi.org/10.1534/g3.118.200961>, PMCID PMC6469405.
