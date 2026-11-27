# Critical curve of the sharp-peak Moran model

Fix a finite alphabet $\mathcal A$ with $\kappa = |\mathcal A| \ge 2$ letters, a chromosome length $\ell$, a population size $m$ and a per-locus mutation probability $q \in (0, 1 - 1/\kappa)$. A mutation at a locus replaces the letter by one of the other $\kappa - 1$ letters chosen uniformly, independently over loci, so the mutation matrix on $\mathcal A^\ell$ is

$$M(u,v) = \prod_{j=1}^{\ell} \Big( (1-q)\,\mathbf 1_{u(j)=v(j)} + \frac{q}{\kappa-1}\,\mathbf 1_{u(j)\neq v(j)} \Big).$$

On the **sharp peak landscape** a master sequence $w^*$ has fitness $A(w^*) = \sigma > 1$ and every other chromosome has fitness $1$. The **Moran model** is the Markov process on populations $x = (x(1),\dots,x(m)) \in (\mathcal A^\ell)^m$ with generator

$$\mathcal L\phi(x) = \sum_{i,j=1}^{m} \sum_{u \in \mathcal A^\ell} A(x(i))\, M(x(i),u)\, \big(\phi(x(j \leftarrow u)) - \phi(x)\big),$$

where $x(j \leftarrow u)$ replaces the $j$-th chromosome by $u$: individual $i$ reproduces at rate $A(x(i))$, its offspring is mutated by $M$ and replaces a uniformly chosen individual $j$. The process is irreducible on a finite space; let $N(x)$ be the number of copies of $w^*$ in $x$ and set

$$\mathrm{Master}(\sigma,\ell,m,q) = \lim_{t\to\infty} E\Big(\frac{N(X_t)}{m}\Big), \qquad \mathrm{Variance}(\sigma,\ell,m,q) = \lim_{t\to\infty} E\Big(\Big(\frac{N(X_t)}{m} - \mathrm{Master}\Big)^2\Big).$$

Define $\phi : [0,\infty) \to [0,\infty]$ by $\phi(a) = 0$ for $a \ge \ln\sigma$ and, for $a < \ln\sigma$,

$$\phi(a) = \frac{\sigma(1-e^{-a}) \ln \dfrac{\sigma(1-e^{-a})}{\sigma-1} + \ln(\sigma e^{-a})}{1 - \sigma(1-e^{-a})}.$$

**Theorem (Cerf, Theorem 3.1).** Let $\ell \to \infty$, $m \to \infty$ and $q \to 0$ in such a way that $\ell q \to a \in (0,\infty)$ and $m/\ell \to \alpha \in [0,\infty]$.

- If $\alpha\,\phi(a) < \ln\kappa$, then $\mathrm{Master}(\sigma,\ell,m,q) \to 0$.
- If $\alpha\,\phi(a) > \ln\kappa$, then

$$\mathrm{Master}(\sigma,\ell,m,q) \to \frac{\sigma e^{-a} - 1}{\sigma - 1}.$$

In both cases $\mathrm{Variance}(\sigma,\ell,m,q) \to 0$. The result holds for the continuous-time process and for the discrete-time chain with the same stationary law.

The **critical curve** $\{(a,\alpha) : \alpha\,\phi(a) = \ln\kappa\}$ separates a phase where the equilibrium population is neutral (no quasispecies) from a phase where a quasispecies concentrated around $w^*$ is present. In particular $\alpha\,\phi(a) > \ln\kappa$ forces $a < \ln\sigma$, so the limiting master density above is positive.

## Depends on

- [Eigen's error threshold](../../../../eigen-s-quasispecies-error-threshold/master-equilibrium-exp-pos-iff.md)

## Expansion

The heuristic is a competition between two time scales. Starting from a population containing the master sequence, the **persistence time** is the time until all master copies are lost; it is governed by selection and grows like $\exp(m\,\phi(a))$, the inverse of the fixation probability of a non-master type computed from a birth-and-death chain for the master count. Starting from a neutral population, the **discovery time** is the time until mutation creates $w^*$; the population must explore a large part of $\mathcal A^\ell$, so this time is of order $\kappa^\ell$. A quasispecies forms when persistence dominates discovery, that is when $m\,\phi(a) > \ell\ln\kappa$ asymptotically, which is $\alpha\,\phi(a) > \ln\kappa$. The proof makes this rigorous by lumping the Moran process into the occupancy process (counts of chromosomes at each Hamming distance from $w^*$), which is monotone for $\sigma \ge 1$, and sandwiching it between lower and upper processes that behave as birth-and-death chains once a master sequence is present. In the quasispecies phase the limit $(\sigma e^{-a}-1)/(\sigma-1)$ is the same master density as in Eigen's deterministic model on the sharp peak in the long-chain limit.

## Sources

- R. Cerf, *Critical population and error threshold on the sharp peak landscape for a Moran model*, arXiv:1205.3435 (2012). <https://doi.org/10.48550/arXiv.1205.3435>. Published version: Memoirs of the American Mathematical Society 233(1096) (2014), <https://doi.org/10.1090/memo/1096>; locators above refer to the arXiv version.
