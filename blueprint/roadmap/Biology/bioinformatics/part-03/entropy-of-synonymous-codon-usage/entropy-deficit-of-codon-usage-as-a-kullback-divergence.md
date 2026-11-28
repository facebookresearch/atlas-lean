# Entropy deficit of codon usage as a Kullback divergence

Let $I$ be a finite set (the 61 sense codons), let $\alpha$ be a partition of $I$ (codons grouped by the amino acid they encode) and let $\beta$ be a strictly finer partition, $\beta\succ\alpha$, so that every atom $A\in\alpha$ is a union of atoms of $\beta$. Write $N^\beta(A)=|\{B\in\beta: B\subseteq A\}|$ for the number of $\beta$-atoms inside $A$, and fix an amino-acid distribution $q=(q_A)_{A\in\alpha}$ with $q_A>0$. A distribution $r=(r_B)_{B\in\beta}$ *extends* $q$ if $\sum_{B\subseteq A} r_B=q_A$ for every $A\in\alpha$. With Shannon entropy $h(\alpha,q)=-\sum_A q_A\log q_A$, the conditional entropy of an extension is

$$h_r(\beta\mid\alpha)=h(\beta,r)-h(\alpha,q)=-\sum_{A\in\alpha}q_A\sum_{B\subseteq A}\frac{r_B}{q_A}\log\frac{r_B}{q_A}.$$

**Maximal-entropy extension.** The extension $r^M_B=q_{A}/N^\beta(A)$ for $B\subseteq A$ (uniform usage of synonymous codons) maximizes $h(\beta,r)$ over all extensions of $q$, with $h(\beta,r^M)=\sum_{A}q_A\log N^\beta(A)+h(\alpha,q)$.

**Entropy deficit.** The codon-usage-bias statistic is

$$\Delta^q(\beta,r)=h(\beta,r^M)-h(\beta,r)=\sum_{A\in\alpha}q_A\log N^\beta(A)-h_r(\beta\mid\alpha),$$

and $\Delta=\Delta^q(\mathcal D,r)$ when $\beta$ is the discrete partition $\mathcal D$ of codons. It satisfies $0\le\Delta^q(\beta,r)\le\sum_A q_A\log N^\beta(A)$, vanishes exactly when $r$ is constant on the $\beta$-atoms of each amino acid, and attains the upper bound exactly when each amino acid uses a single codon class.

**Theorem (Kullback representation).** For every extension $r$ of $q$,

$$\Delta^q(\beta,r)=\sum_{B\in\beta}r_B\log\frac{r_B}{r^M_B}=D_{\mathrm{KL}}(r\,\|\,r^M),$$

the squared Kullback distance between $r$ and the uniform-synonymous extension. Consequently, by $D_{\mathrm{KL}}\le\chi^2$,

$$\Delta^q(\beta,r)\le\sum_{A\in\alpha}q_A\,N^\beta(A)\,\mathrm{hz}_A(\beta)-1,\qquad \mathrm{hz}_A(\beta)=\sum_{B\subseteq A}\Big(\frac{r_B}{q_A}\Big)^2,$$

where $\mathrm{hz}_A(\beta)$ is the homozygosity of amino acid $A$, the quantity underlying the effective number of codons.

## Expansion

For $i\in B\subseteq A$ the Radon–Nikodym derivative is $dr/dr^M=N^\beta(A)\,r_B/q_A$. Summing $r_B\log(N^\beta(A)r_B/q_A)$ over $B\subseteq A$ and $A\in\alpha$ gives $h(\alpha,q)-h(\beta,r)+\sum_A q_A\log N^\beta(A)$, which is $\Delta^q(\beta,r)$. The $\chi^2$ bound follows by expanding $\sum_B r^M_B\,(dr/dr^M-1)^2$. Because $q$ is held fixed, $\Delta$ removes amino-acid composition and compares synonymous codon bias across chromosomes; the maximum entropy step is Jensen's inequality for the concave map $x\mapsto -x\log x$ on each amino-acid block.

## Proof depends on

- [Gibbs' inequality](../../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/sum-mul-log-div-nonneg.md)

## Sources

- A. Hart and S. Martínez, *An entropy-based technique for classifying bacterial chromosomes according to synonymous codon usage*, arXiv:1510.04180 (2015), Section 2 and Proposition 1 (Section 2.1). <https://doi.org/10.48550/arXiv.1510.04180>
