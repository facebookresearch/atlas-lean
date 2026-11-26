# Optimal coverage for haplotype assembly via convolutional code free distance

**Model.** As for adjacent-SNP mate-pairs ($n$ heterozygous SNPs, parities $L_i=S_i\oplus S_{i+1}$, per-SNP read error $p$, $\theta=2p(1-p)$, $D(\theta)=D(\tfrac12\|\theta)$, $\mathrm{Poisson}(c\,n\ln n)$ reads), but now a mate-pair covers SNPs $i$ and $i+W$ with $W\in\{1,\dots,w\}$ random and independent of $i$. The read reports $S_i\oplus S_{i+W}=L_i\oplus\dots\oplus L_{i+W-1}$ through a binary symmetric channel. Thus the observations are a rate-$1/w$ convolutional code with polynomial generator matrix

$$g_w(z)=\big[\,1,\ 1+z,\ \dots,\ 1+z+\dots+z^{w-1}\,\big],$$

each output repeated a Poisson number of times. For stream probabilities $\mathbf p=(p_1,\dots,p_w)$, $p_j=\mathbb P(W=j)$, the *averaged free distance* is $\tilde d_{\mathrm{free}}=\min_{v\ne0}\sum_jp_j\,\mathrm{wt}(v^{(j)})$ over nonzero codewords.

**Theorem.**

*(1)* If $W\in\{1,2\}$ with probability $\tfrac12$ each, the optimal coverage is $c(p)=\dfrac{2/3}{1-e^{-D(\theta)}}$.

*(2)* The code $g_w$ has free distance $2w$ for $w\ge3$, and if $W$ is uniform on $\{1,\dots,w\}$ with $w\ge3$, then $c(p)=\dfrac{w}{d_{\mathrm{free}}(1-e^{-D(\theta)})}=\dfrac{1/2}{1-e^{-D(\theta)}}$.

*(3)* For general $\mathbf p$ such that the generator polynomials on the support of $\mathbf p$ have greatest common divisor $1$ (non-catastrophic code), $\tilde d_{\mathrm{free}}=\min\{\mathbb E[W],2\}$ and

$$c(p)=\frac1{\tilde d_{\mathrm{free}}\,(1-e^{-D(\theta)})}=\frac1{\min\{\mathbb E[W],2\}\,(1-e^{-D(\theta)})}.$$

Linking more distant SNPs therefore lowers the required coverage by a factor up to $2$, beyond which longer inserts do not help.

## Depends on

- [Optimal coverage for haplotype assembly from adjacent-SNP mate-pairs](optimal-coverage-for-haplotype-assembly-from-adjacent-snp-mate-pairs.md)

## Expansion

Haplotype assembly is ML decoding of the convolutional code with the Viterbi algorithm on a trellis with $2^{w-1}$ states, except that the code cannot be zero-terminated because the SNP values are given. As in the adjacent case, the analysis is a union bound over error events of the trellis: an error event whose codeword differs from the truth in averaged weight $d$ is supported by a Poisson number of observations proportional to $d\,c\ln n$, so it has probability about $n^{-c\,d(1-e^{-D(\theta)})}$; with $O(n)$ starting positions, the minimum-weight events decide the threshold $c\,\tilde d_{\mathrm{free}}(1-e^{-D(\theta)})=1$, and a matching lower bound holds even for the ML decoder. The weight computation: a single-monomial input produces weight $j$ on stream $j$ (averaged weight $\mathbb E[W]$), while any input with two or more monomials has weight at least $2$ on every stream, attained by $1+z$; for $w\ge3$ a monomial gives total weight $w(w+1)/2>2w$, so $d_{\mathrm{free}}=2w$. For $w=2$ the free distance is $3$, giving $\frac{2}{3}$.

## Sources

- G. M. Kamath, E. Şaşoğlu, D. Tse, "Optimal haplotype assembly from high-throughput mate-pair reads", arXiv:1502.01975 (2015), <https://doi.org/10.48550/arXiv.1502.01975>. Section 4 (Theorem 4.1, Lemma 4.2, Theorem 4.3, Lemma 4.4, Theorem 4.5) and Section 5 (non-uniform SNP coverage example).
