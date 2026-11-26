# Expected codon-usage entropy under uniform Dirichlet extensions

Fix a finite codon set $I$, the amino-acid partition $\alpha$ of $I$, a partition $\beta\succeq\alpha$, and an amino-acid distribution $q=(q_A)_{A\in\alpha}$. Model *a priori ignorance* of synonymous usage by a random codon distribution $P=(P_i)_{i\in I}$ extending $q$ such that, independently over $A\in\alpha$,

$$q_A^{-1}(P_i)_{i\in A}\sim\mathrm{Dirichlet}(1,\dots,1)\quad(|A|\text{ ones}),$$

that is, the within-amino-acid usage vector is uniform on the simplex of dimension $|A|-1$. Let $\xi_n=\sum_{j=1}^n j^{-1}$ be the $n$-th harmonic number and $N^\beta(A)$ the number of $\beta$-atoms in $A$.

**Theorem.** The expected conditional entropy of $P$ restricted to $\beta$ is

$$\mathbb E\big[h_P(\beta\mid\alpha)\big]=\sum_{A\in\alpha}q_A\,\xi_{|A|}-\sum_{A\in\alpha}\frac{q_A}{|A|}\sum_{B\in\beta:\,B\subseteq A}|B|\,\xi_{|B|}.$$

**Corollary.** With $h(\alpha,q)=-\sum_A q_A\log q_A$ and the entropy deficit $\Delta^q(\beta,P)=\sum_A q_A\log N^\beta(A)-h_P(\beta\mid\alpha)$ (the distance of $P$ from uniform synonymous usage),

$$\mathbb E\big[h(\beta,P)\big]=h(\alpha,q)+\sum_{A}q_A\xi_{|A|}-\sum_{A}\frac{q_A}{|A|}\sum_{B\subseteq A}|B|\xi_{|B|},$$

$$\mathbb E\big[\Delta^q(\beta,P)\big]=\sum_{A}q_A\log N^\beta(A)-\sum_{A}q_A\xi_{|A|}+\sum_{A}\frac{q_A}{|A|}\sum_{B\subseteq A}|B|\xi_{|B|}.$$

For the discrete partition $\beta=\mathcal D$ (all $|B|=1$) this reduces to $\mathbb E[\Delta]=\sum_A q_A\big(\log|A|-\xi_{|A|}+1\big)$, the null level against which an observed genome's codon-usage bias is compared.

## Expansion

Aggregation property of the Dirichlet law: if $Y\sim\mathrm{Dirichlet}(1,\dots,1)$ on $a$ coordinates and $Z=\sum_{j\in J}Y_j$ with $|J|=b$, then $Z\sim\mathrm{Beta}(b,a-b)$ (via the Gamma construction $Y_j=G_j/\sum G_i$). Using $\mathbb E[Z\log Z]=\frac{b}{a}\big(\psi(b+1)-\psi(a+1)\big)$ and $\psi(n+1)=\xi_n-\gamma$, one gets $\mathbb E[-Z\log Z]=\frac{b}{a}(\xi_a-\xi_b)$. Applying this to each $B\subseteq A$ with $a=|A|$, $b=|B|$, weighting by $q_A$, and summing yields the theorem. The corollary adds the deterministic terms $h(\alpha,q)$ and $\sum_A q_A\log N^\beta(A)$. The paper complements this with an Azuma–Hoeffding lower-tail bound for $\Delta^q(\beta,P)$ along dyadic refinements (Theorem 4), but notes that for bacterial genomes the bound is too loose for practical use (Remark 9).

## Depends on

- [Entropy deficit of codon usage as a Kullback divergence](entropy-deficit-of-codon-usage-as-a-kullback-divergence.md)
- [Dirichlet distribution](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Sources

- A. Hart and S. Martínez, *An entropy-based technique for classifying bacterial chromosomes according to synonymous codon usage*, arXiv:1510.04180 (2015), Section 3, Theorem 2 and Corollary 3. <https://doi.org/10.48550/arXiv.1510.04180>
