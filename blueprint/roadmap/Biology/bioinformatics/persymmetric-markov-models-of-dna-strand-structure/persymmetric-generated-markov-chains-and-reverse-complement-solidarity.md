# Persymmetric-generated Markov chains and reverse-complement solidarity

Identify nucleotides with $N=\{1,2,3,4\}$ ($A,C,G,T$) and let $\alpha(i)=5-i$ be Watson–Crick complementation. A positive $4\times4$ matrix $L$ is *persymmetric* if $L_{ij}=L_{\alpha(j)\alpha(i)}$ for all $i,j$; let $\aleph$ be the cone of such matrices. For $L\in\aleph$ and $m>0$ define the stochastic matrix

$$\digamma(L,m)_{ij}=\frac{L_{ij}M_j}{\sum_{k}L_{ik}M_k},\qquad M_1=M_4=\frac{m}{2m+2},\quad M_2=M_3=\frac{1}{2m+2}.$$

A stochastic matrix $P$ is *$\aleph$-generated* if $P=\digamma(L,m)$ for some $(L,m)$. This is the transition matrix of the Sobottka–Hart concatenation model of bacterial chromosomes: a nucleotide of type $j$ is drawn with probability $M_j$ and is appended after a terminal nucleotide $i$ with probability $L_{ij}$, or prepended before an initial nucleotide $k$ with probability $L_{\alpha(k)\alpha(j)}$; the half-sequence grown after the origin is the stationary chain $(P,\pi)$.

**Characterizations.**
1. *Fibres.* For $\aleph$-generated $P$, $\digamma^{-1}(P)=\{(\tilde s\,\varphi(P,\tilde m),\tilde m):\tilde m,\tilde s>0\}$, where $\varphi(P,\tilde m)\in\aleph$ is an explicit matrix built from the nine ratios $P_{ij}/P_{i\alpha(j)}$, $P_{14}/P_{13}$ and $P_{23}/P_{24}$; the generator is unique up to the two free parameters $\tilde m,\tilde s$.
2. *Diagonal scaling.* $P$ is $\aleph$-generated if and only if $D(\mathbf{x})P\in\aleph$ for some strictly positive vector $\mathbf{x}$ (here $D(\mathbf{x})$ is the diagonal matrix with diagonal $\mathbf{x}$); equivalently, $P$ is the row normalization of $\varphi(P,1)$.

**Solidarity theorem.** For a stationary chain $(P,\pi)$ let $P^\alpha_{ij}=P_{\alpha(i)\alpha(j)}$ (complement), $P^*_{ij}=\pi_jP_{ji}/\pi_i$ (reverse) and $\tilde P_{ij}=\pi_{\alpha(j)}P_{\alpha(j)\alpha(i)}/\pi_{\alpha(i)}$ (reverse complement). Then $P$, $P^\alpha$, $P^*$ and $\tilde P$ are either all $\aleph$-generated or none of them is.

Consequently, in the concatenation model both chirochores (the replication-defined halves of a bacterial chromosome, approximated by $(P,\pi)$ and by its reverse complement $(\tilde P,\tilde\pi)$) are described by $\aleph$-generated chains.

## Expansion

For the complement, $P^\alpha=\digamma(L^\alpha,1)$ with $L^\alpha_{ij}=L_{\alpha(i)\alpha(j)}$, which is again persymmetric. For the reverse, the diagonal scaling criterion applies with $\mathbf{x}=(P^*_{44}/P^*_{11},P^*_{43}/P^*_{21},P^*_{42}/P^*_{31},1)$: persymmetry of $D(\mathbf{x})P^*$ reduces to an identity among the row sums of $L$. The reverse complement is the reverse of the complement, and all three operations are involutions, which gives the all-or-none statement.

## Sources

- A. G. Hart and M. Sobottka, *A Markovian genomic concatenation model guided by persymmetric matrices*, arXiv:1805.02231 (2018), <https://doi.org/10.48550/arXiv.1805.02231>. Definition 3; Theorem 4 (fibres of $\digamma$); Corollaries 5 and 6; Theorem 11 (solidarity).
