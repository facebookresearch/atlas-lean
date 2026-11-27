# Moment equations for the neutral sample frequency spectrum

Let $\varphi(x,t)$ be the density of derived-allele frequencies $x \in (0,1)$ in a diploid population of size $N$ under the infinite-sites model with genome-wide mutation rate $u$ per generation, evolving by the forward Wright–Fisher diffusion

$$\partial_t \varphi = \frac{1}{4N}\, \partial_x^2\big[x(1-x)\varphi\big] + 2Nu\,\delta\!\left(x - \tfrac{1}{2N}\right).$$

For a sample of $n$ haploid copies define the expected sample frequency spectrum

$$\Phi_n(i) = \int_0^1 \binom{n}{i} x^i (1-x)^{n-i} \varphi(x,t)\, dx, \qquad 1 \le i \le n-1.$$

**Theorem (closed neutral moment equations).** If $\varphi$ is regular enough that the boundary terms of two integrations by parts vanish, the vector $\Phi_n = (\Phi_n(1), \dots, \Phi_n(n-1))$ satisfies the closed linear system

$$\dot\Phi_n(i) = \frac{1}{4N}\Big[(i-1)(n-i+1)\,\Phi_n(i-1) - 2i(n-i)\,\Phi_n(i) + (n-i-1)(i+1)\,\Phi_n(i+1)\Big] + U_n(i), \qquad U_n(i) = 2Nu\binom{n}{i}\Big(\frac{1}{2N}\Big)^{i}\Big(1 - \frac{1}{2N}\Big)^{n-i},$$

with $\Phi_n(0) = \Phi_n(n) = 0$ in the bracket. The forcing $U_n(i)$ is the projection of the point source onto $w_{n,i}$. To leading order in $1/N$ it is $U_n(i) = nu\,\delta_{i,1} + O(u/N)$, since $U_n(1) = nu\,(1 - \tfrac{1}{2N})^{n-1}$ and, for $i \ge 2$, $U_n(i) = O(u\, n^i N^{1-i})$; for $n \ge 3$ and $u > 0$, $U_n(2) > 0$, so the version with source $nu\,\delta_{i,1}$ is the leading-order approximation used in practice, not an exact consequence of the diffusion. For $p$ populations with sizes $N_j$, sample sizes $n = (n_1,\dots,n_p)$ and migration rates $m_{jk}$, the joint spectrum obeys the same drift operator in each coordinate plus mutation sources at $i = e_j$ and migration terms $m_{jk}\mathcal{M}_{jk}\Phi_{n + e_j}$ that involve the spectrum at one larger sample size.

## Proof sketch

Differentiate under the integral and integrate the drift term by parts twice against $w_{n,i}(x) = \binom{n}{i}x^i(1-x)^{n-i}$; because $w_{n,i}$ vanishes at $0$ and $1$ for $1 \le i \le n-1$ the boundary terms drop. The second derivative $w_{n,i}''$ multiplied by $x(1-x)$ is a combination of $w_{n,i-1}$, $w_{n,i}$ and $w_{n,i+1}$ with coefficients $(i-1)(n-i+1)$, $-2i(n-i)$ and $(n-i-1)(i+1)$, which gives the tridiagonal drift operator. Integrating the point source against $w_{n,i}$ evaluates $w_{n,i}$ at $x = 1/(2N)$, which gives $U_n(i)$; it contributes $n u$ to $i = 1$ at leading order in $1/N$. The same system arises without the diffusion limit: in a Wright–Fisher generation the $n$ sampled copies descend from $n$ distinct parents unless one pair shares a parent (probability about $\binom{n}{2}/(2N)$), and conditioning on this event gives the same one-generation recursion. The equations are algebraically equivalent to the classical moment equations for $\int x^k\varphi\,dx$, but the binomial basis avoids alternating sums and is numerically stable, and neutral drift closes at fixed $n$, so one can integrate the spectrum forward through any size history with $n-1$ unknowns.

## Sources

- J. Jouganous, W. Long, A. P. Ragsdale and S. Gravel, "Inferring the joint demographic history of multiple populations: beyond the diffusion approximation", Genetics 206 (2017), 1549–1567, Equations (1)–(4), Appendix A (Equations (A1) and (A2)) and Appendix C, <https://doi.org/10.1534/genetics.117.200493>, PMCID PMC5500150.
