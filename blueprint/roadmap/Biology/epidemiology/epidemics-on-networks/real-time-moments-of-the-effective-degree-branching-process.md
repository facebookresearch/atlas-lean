# Real-time moments of the effective-degree branching process

Consider the Markovian SIR epidemic on a configuration-model network with degree $D$ (maximum degree $k_{\max}$, mean $\mu_D$): infection passes along each edge from an infective to a susceptible neighbour at rate $\tau$, and infectives recover at rate $\gamma$. Let $\tilde D$ be the size-biased degree, $\tilde p_k=\mathbb P(\tilde D=k)=\mu_D^{-1}kp_k$, and write $\mu_X=\mathbb E[X]$. As the population size tends to infinity the early epidemic is a continuous-time multitype branching process whose type $k$ is an infective's **effective degree** (number of susceptible neighbours). A type-$k$ individual has an event at rate $\omega_k=\gamma+\tau k$; it recovers with probability $\gamma/\omega_k$, and otherwise becomes type $k-1$ and creates a new infective of type $l$ with probability $\tilde p_{l+1}$.

**Theorem (mean prevalence).** Let $r=\tau\mu_{\tilde D-2}-\gamma$ be the Malthusian parameter and $\mathbf n=(0,1,\dots,k_{\max})^\top$. If $r\neq-\gamma$, the expected number of infectives at time $t$ started from one type-$k$ infective is

$$\mathbb E\bigl[Z^{(k)}(t)\bigr]=\frac{k}{\mu_{\tilde D-2}}\bigl(e^{rt}-e^{-\gamma t}\bigr)+e^{-\gamma t},$$

so $e^{-rt}\,\mathbb E[Z^{(k)}(t)]\to k/\mu_{\tilde D-2}$. Equivalently, prevalence $I(t)$ and the number $\lambda(t)$ of susceptible–infective edges obey $\dot I=\tau\lambda-\gamma I$, $\dot\lambda=r\lambda$. The mean depends on the degree distribution only through its first two moments.

**Theorem (variance).** The variance of $Z^{(k)}(t)$ has the closed form $\alpha_0(t)+\alpha_1(t)k+\alpha_2(t)k^2$ with explicit exponential-polynomial coefficients; for $r>0$ its asymptotic squared coefficient of variation is

$$\lim_{t\to\infty}\frac{\operatorname{var}(Z^{(k)}(t))}{\mathbb E[Z^{(k)}(t)]^2}=\frac{1}{2\mu_{\tilde D-1}\tau-\gamma}\Bigl[\gamma+\frac{2\tau\mu_{\tilde D-1}\bigl(\mu_{(\tilde D-2)^2}\tau+\gamma\bigr)}{kr}\Bigr],$$

which depends on the first three moments of $D$.

**Extinction by time $t$.** The probabilities $\pi_k(t)=\mathbb P(Z^{(k)}(t)=0)$, $\pi_k(0)=0$, solve

$$\frac{d\pi_k}{dt}=-(\gamma+\tau k)\pi_k+\gamma+\tau k\,\pi_{k-1}\sum_{l=0}^{k_{\max}-1}\tilde p_{l+1}\pi_l .$$

## Expansion

The mean matrix $\mathbf M(t)=e^{\boldsymbol\Omega t}$ solves $\dot{\mathbf M}=\mathbf M\boldsymbol\Omega$. Rather than diagonalizing $\boldsymbol\Omega$, note that $\boldsymbol\Omega\mathbf 1=\tau\mathbf n-\gamma\mathbf 1$ and $\boldsymbol\Omega\mathbf n=r\mathbf n$; for any matrix with $\mathbf M\mathbf x=a\mathbf x+b\mathbf y$ and $\mathbf M\mathbf y=c\mathbf y$, $a\ne c$, the series gives $e^{\mathbf Mt}\mathbf x=e^{at}\mathbf x+\frac{b}{a-c}(e^{at}-e^{ct})\mathbf y$. With $a=-\gamma$, $b=\tau$, $c=r$ and $r+\gamma=\tau\mu_{\tilde D-2}$ this is the mean formula. The variance follows from the standard integral representation of second moments of Markov branching processes, in which the same two-dimensional invariant subspace, extended by $\mathbf n_2=(i^2)_i$, keeps everything explicit. The extinction equations are the Kolmogorov backward equations $\dot\pi_k=\omega_k(P_k(\boldsymbol\pi)-\pi_k)$ for the offspring generating functions $P_k$. These results hold for any number of initial infectives, not only in the large-outbreak regime.

## Sources

- F. Ball and T. House, "Heterogeneous network epidemics: real-time growth, variance and extinction of infection", Journal of Mathematical Biology 75(3) (2017) 577–619, <https://doi.org/10.1007/s00285-016-1092-3>, PMCID PMC5532454. Eqs. (2.1)–(2.3), Proposition 1, Eqs. (3.4) and (3.13)–(3.18), (4.4)–(4.8) and (7.1)–(7.2).
