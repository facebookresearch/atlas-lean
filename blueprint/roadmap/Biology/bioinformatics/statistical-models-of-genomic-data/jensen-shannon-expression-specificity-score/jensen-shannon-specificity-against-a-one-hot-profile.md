# Jensen–Shannon specificity against a one-hot expression profile

Let gene $i$ have nonnegative mean expression $x_{i,1},\dots,x_{i,n}$ in $n$ groups, not all zero, and let $p=(p_1,\dots,p_n)$, $p_k=x_{i,k}/\sum_l x_{i,l}$, be its expression profile. For a group $j$ let $e_j$ be the one-hot profile ($e_{j,k}=1$ if $k=j$ and $0$ otherwise). With $M=\tfrac12(p+e_j)$, the Jensen–Shannon divergence in bits is

$$\mathrm{JSD}(p,e_j)=\tfrac12\,\mathrm{KL}(p\,\|\,M)+\tfrac12\,\mathrm{KL}(e_j\,\|\,M)=1+\tfrac12\bigl[p_j\log_2p_j-(1+p_j)\log_2(1+p_j)\bigr],$$

with $0\log_20=0$. Consequently:

1. $\mathrm{JSD}(p,e_j)$ depends on $p$ only through the share $p_j$ of group $j$;
2. it is strictly decreasing in $p_j$, from $1$ at $p_j=0$ to $0$ at $p_j=1$;
3. the specificity score $\mathrm{S}_{i,j}=-\log_{10}\mathrm{JSD}(p,e_j)$ ranks genes for a fixed group $j$ exactly as the share $p_j=x_{i,j}/\sum_k x_{i,k}$ does, and is infinite only for expression confined to group $j$.

## Depends on

- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof sketch

Since $M_j=(1+p_j)/2$ and $M_k=p_k/2$ for $k\ne j$, $\mathrm{KL}(p\|M)=\sum_{k\ne j}p_k\log_22+p_j\log_2\frac{2p_j}{1+p_j}$ and $\mathrm{KL}(e_j\|M)=\log_2\frac{2}{1+p_j}$; adding and using $\sum_{k\ne j}p_k=1-p_j$ gives the closed form. Its derivative in $p_j$ is $\tfrac12\log_2\frac{p_j}{1+p_j}<0$. So the distribution of expression over the other groups is irrelevant: a gene split evenly between two other groups and one concentrated in a single other group get the same score. The source's cancer core transcription-factor score is $\mathrm{S}_{i,j}$ computed on transcription-factor expression averaged by tumor type over 34 types, after shifting values to a minimum of zero and replacing zeros by a tiny constant (which perturbs the closed form only negligibly). It takes as candidate master transcription factors those in the top 5% both by the score and by expression level in that tumor type, and assesses scores against permutations of sample-to-type labels. The closed form and the ranking equivalence are derived here; the source states the score definition only.

## Sources

- J. Reddy, M. A. S. Fonseca, R. I. Corona, R. Nameki, F. Segato Dezem, I. A. Klein, H. Chang, D. Chaves-Moreira, L. K. Afeyan, T. M. Malta, et al., "Predicting master transcription factors from pan-cancer expression data", Science Advances 7 (2021), eabf6123, Methods ("The CaCTS algorithm", "Bootstrapping and t test methods for the statistical assessment of the CaCTS score"), <https://doi.org/10.1126/sciadv.abf6123> (PMC8612691).
