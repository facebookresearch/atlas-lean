# Optimal coverage for haplotype assembly from adjacent-SNP mate-pairs

**Model.** A diploid chromosome carries $n$ SNPs, all heterozygous: one homologue has alleles $S_1,\dots,S_n\in\{0,1\}$ and the other $S_1^c,\dots,S_n^c$. The haplotype is determined up to swapping homologues by the parities $L_i=S_i\oplus S_{i+1}$, $1\le i\le n-1$. Each aligned mate-pair read covers SNPs $i,i+1$ with $i$ uniform in $\{1,\dots,n-1\}$, comes from either homologue with probability $\tfrac12$, and each of its two SNP calls is wrong independently with probability $p$. The number of reads is $\mathrm{Poisson}(c\,(n-1)\ln n)$. $c(p)$ is the *optimal coverage* if for every $\epsilon>0$, $(c(p)-\epsilon)n\ln n$ reads do not suffice to reconstruct with probability at least $1-\epsilon$, while $(c(p)+\epsilon)n\ln n$ reads do, as $n\to\infty$.

**Theorem.** Let $\theta=2p(1-p)$ be the probability that a read reports the wrong parity and $D(\theta)=D(\tfrac12\,\|\,\theta)$ the relative entropy in nats. Then

$$c(p)=\frac1{1-e^{-D(\theta)}}$$

is the optimal coverage. In the noiseless case $p=0$, reconstruction is the coupon collector problem on $n-1$ adjacent pairs, so $c(n-1)\log(n-1)$ reads succeed with high probability for $c>1$ and fail for $c<1$; at $p=\tfrac12$ no finite coverage suffices.

## Expansion

The observed parities of pair $i$ are $N_i\sim\mathrm{Poisson}(c\ln n)$ independent copies of $L_i$ sent through a binary symmetric channel with crossover $\theta$, a repetition code, and the ML rule is a majority vote. Chernoff and method-of-types bounds give $\frac{1}{2(N_i+1)^2}e^{-N_iD(\theta)}\le\mathbb P(\text{wrong }L_i\mid N_i)\le e^{-N_iD(\theta)}$, and averaging over the Poisson $N_i$ gives $\mathbb P(\text{wrong }L_i)\approx n^{-c(1-e^{-D(\theta)})}$. A union bound over the $n-1$ pairs succeeds when $c(1-e^{-D(\theta)})>1$, and independence of the pairs under Poisson splitting makes some pair fail with high probability when $c(1-e^{-D(\theta)})<1$.

## Sources

- G. M. Kamath, E. Şaşoğlu, D. Tse, "Optimal haplotype assembly from high-throughput mate-pair reads", arXiv:1502.01975 (2015), <https://doi.org/10.48550/arXiv.1502.01975>. Section 2 (noiseless coupon-collector case) and Section 3 (Theorem 3.1).
