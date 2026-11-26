# Fixation probabilities of the incentive process

**Definition.** A population of fixed size $N$ has $i$ individuals of type $A$ and $N-i$ of type $B$. An *incentive* is a pair of functions $\varphi_A(i),\varphi_B(i)\ge0$. The incentive process is the birth–death Markov chain on $\{0,\dots,N\}$ in which the reproducing type is chosen in proportion to its incentive and the dying individual uniformly at random:

$$T_{i\to i+1}=\frac{\varphi_A(i)}{\varphi_A(i)+\varphi_B(i)}\cdot\frac{N-i}{N},\qquad T_{i\to i-1}=\frac{\varphi_B(i)}{\varphi_A(i)+\varphi_B(i)}\cdot\frac{i}{N},$$

and $T_{i\to i}=1-T_{i\to i+1}-T_{i\to i-1}$. The Moran process is the incentive $\varphi_A(i)=if_A(i)$, $\varphi_B(i)=(N-i)f_B(i)$ for fitness landscapes $f_A,f_B$, e.g. from a $2\times2$ game. Other choices give stochastic versions of familiar deterministic dynamics, with $x_A=i$, $x_B=N-i$:

- projection: $\varphi_T=f_T$;
- $q$-replicator: $\varphi_T=x_T^{\,q}f_T$ ($q=1$ is the Moran process);
- $q$-Fermi: $\varphi_T\propto x_T^{\,q}e^{\beta f_T}$ ($q=1$ is the Fermi process, $q=0$ the logit incentive);
- best reply: the limit $\beta\to\infty$ of the $q$-Fermi.

Assume $\varphi_A(k),\varphi_B(k)>0$ for $0<k<N$.

**Fixation formula.** The probability that type $A$ fixes from state $i$ is

$$\rho_i=\frac{\sum_{j=0}^{i-1}t_j}{\sum_{j=0}^{N-1}t_j},\qquad t_j=\prod_{k=1}^{j}\frac{k\,\varphi_B(k)}{(N-k)\,\varphi_A(k)}=\binom{N-1}{j}^{-1}\prod_{k=1}^{j}\frac{\varphi_B(k)}{\varphi_A(k)} ,$$

with $t_0=1$. Writing $\rho_A=\rho_1$ and $\rho_B=1-\rho_{N-1}$ for the fixation probabilities of a single mutant of either type,

$$\frac{\rho_B}{\rho_A}=t_{N-1}=\prod_{k=1}^{N-1}\frac{k\,\varphi_B(k)}{(N-k)\,\varphi_A(k)} .$$

**Closed forms on the neutral landscape** ($f_A=f_B$) for the $q$-replicator incentive:

$$\rho_{q=0}(N)=\Big(\sum_{k=0}^{N-1}\binom{N-1}{k}^{-1}\Big)^{-1}=\frac{2^N}{N}\Big(\sum_{k=1}^{N}\frac{2^k}{k}\Big)^{-1},\qquad \rho_{q=1}=\frac1N,\qquad \rho_{q=2}=2^{1-N},\qquad \rho_{q=3}=\binom{2N-2}{N-1}^{-1}.$$

For $N>2$ these are strictly ordered, $\rho_{q=3}<\rho_{q=2}<\rho_{q=1}<\rho_{q=0}$, and $1/N<\rho_{q=0}<1/2$ with $\rho_{q=0}(N)\to1/2$: under the projection incentive a single neutral mutant fixes with probability bounded away from zero, unlike the neutral Moran value $1/N$. On the Moran landscape $f_A=r$, $f_B=1$, the $2$-replicator incentive gives $\rho_A=(1+1/r)^{1-N}$, and any $q$-replicator closed form gives the $q$-Fermi one under $r\mapsto e^{\beta(r-1)}$.

## Expansion

The fixation formula is the standard first-step solution for a birth–death chain, with ratios $\gamma_k=T_{k\to k-1}/T_{k\to k+1}=\frac{k\varphi_B(k)}{(N-k)\varphi_A(k)}$; the uniform-death factors contribute $\prod_{k\le j}\frac{k}{N-k}=\binom{N-1}{j}^{-1}$. On the neutral landscape the $q$-replicator incentive has $\prod_{k\le j}\varphi_B(k)/\varphi_A(k)=\prod_{k\le j}\big(\frac{N-k}{k}\big)^q=\binom{N-1}{j}^{q}$, so $t_j=\binom{N-1}{j}^{q-1}$ and

$$\rho_q(N)=\Big(\sum_{j=0}^{N-1}\binom{N-1}{j}^{q-1}\Big)^{-1}.$$

For $q=1,2,3$ the sum is $N$, $2^{N-1}$ and $\sum_j\binom{N-1}{j}^2=\binom{2N-2}{N-1}$. For $q=0$ it is a sum of reciprocal binomial coefficients, which equals $\frac{N}{2^N}\sum_{k=1}^N\frac{2^k}{k}$ and tends to $2$. (The source prints the $q=0$ sum starting at $k=1$; the $k=0$ term is needed, as the check $N=2$, $\rho=1/2$ shows, and the second closed form agrees with the corrected sum.) On the Moran landscape the $2$-replicator gives $t_j=\binom{N-1}{j}r^{-j}$, whose sum is $(1+1/r)^{N-1}$.

## Depends on

- [Fixation probability in a frequency-dependent Moran process](../../population-genetics/moran-model/frequency-dependent-moran-fixation-product-formu.md)

## Sources

- Marc Harper, Dashiell Fryer, "Incentive Processes in Finite Populations", arXiv:1306.2389 (2013): Section 2 (incentive process and incentive table), Section 3 (fixation formula and ratio), Section 3.1 (closed forms). <https://doi.org/10.48550/arXiv.1306.2389>
