# Fitness-valley crossing time under power-law mutation rates

**Model.** Fix a trait space $\mathcal{X}$ and a carrying-capacity parameter $K \in \mathbb{N}$. Each individual with trait $x$ gives birth at rate $b(x) \ge 0$; the offspring is a mutant with probability $p(x)$ (or $u_K p(x)$ when mutation probabilities are scaled with $K$), its trait then drawn from a mutation kernel $m(x,dy)$, and otherwise a clone. Each individual dies at the natural rate $d(x) \ge 0$ plus a competition rate $\frac1K \sum_j c(x, x_j)$ summed over the other individuals. The rescaled population is the finite point measure $\nu^K_t = \frac1K \sum_{i=1}^{N_t} \delta_{x_i(t)} \in \mathcal{M}_F(\mathcal{X})$. For a monomorphic population of trait $x$ with $b(x)>d(x)$ the logistic equilibrium is $\bar n(x) = (b(x)-d(x))/c(x,x)$, and the *invasion fitness* of a mutant $y$ against coexisting residents $\mathbf{x}=(x_1,\dots,x_d)$ at equilibrium $\bar n(\mathbf{x})$ is $f(y,\mathbf{x}) = b(y) - d(y) - \sum_{i} c(y,x_i)\, \bar n_{x_i}(\mathbf{x})$.

**Setting.** Traits $V=\{0,1,\dots,L\}$ with nearest-neighbour forward mutation $m(i,j)=\delta_{i+1,j}$, mutation probability $\mu_K = K^{-1/\alpha}$, and a fitness valley: $f(i,0)<0$ for $1 \le i \le L-1$, $f(L,0)>0$, and $f(i,L)<0$ for $0 \le i \le L-1$. Start from a monomorphic population of size about $\bar n(0) K$ at trait $0$. Let $T^{(K,L)}_a$ be the first time the $L$-population reaches $\lfloor aK\rfloor$, and for valley traits set
$$\rho(i) = \frac{b(i)}{b(i)+d(i)+c(i,0)\bar n(0)}, \qquad \lambda(\rho) = \sum_{k \ge 0} \frac{(2k)!}{(k-1)!(k+1)!}\rho^k(1-\rho)^{k+1} = \frac{\rho}{1-2\rho},$$
so that $\lambda(\rho(i)) = b(i)/|f(i,0)|$.

**Theorem (metastable escape).** Assume $\alpha \notin \mathbb{N}$ and $\alpha < L$. There are constants $\varepsilon_0, c>0$ and exponential random variables $E_\pm(\varepsilon)$ with parameters
$$(1 \pm c\varepsilon)\, \frac{\bar n(0)\, b(0) \cdots b(\lfloor\alpha\rfloor)}{|f(1,0)| \cdots |f(\lfloor\alpha\rfloor,0)|}\; \frac{f(L,0)}{b(L)} \prod_{i=\lfloor\alpha\rfloor+1}^{L-1} \lambda(\rho(i))$$
such that for every $0<\varepsilon\le\varepsilon_0$,
$$\liminf_{K\to\infty} \mathbb{P}\Big(E_-(\varepsilon) \le T^{(K,L)}_{\bar n(L)-\varepsilon}\, K\mu_K^{L} \le E_+(\varepsilon)\Big) \ge 1 - c\varepsilon .$$
The fit trait $L$ therefore takes over after an exponentially distributed time of order $1/(K\mu_K^L)$.

## Depends on

- [Polymorphic evolution sequence](polymorphic-evolution-sequence.md)

## Expansion

Traits $i \le \lfloor\alpha\rfloor$ settle at sizes of order $K\mu_K^i$, mutation supply balancing the negative growth rate $f(i,0)$. Beyond $\lfloor\alpha\rfloor$, each population is an excursion of a subcritical birth–death process whose expected number of births before extinction is $\lambda(\rho(i))$, so it yields a next mutant with probability about $\mu_K\lambda(\rho(i))$. Thinning the stream of attempts by these probabilities and by the survival probability $f(L,0)/b(L)$ of the first $L$-mutant gives the exponential law; the subsequent invasion takes only $O(\ln K)$ time.

## Sources

- A. Bovier, A. Kraut, "Stochastic individual-based models", arXiv:2607.11520, Chapter 8, fitness-valley assumption and Theorem 8.4. <https://doi.org/10.48550/arXiv.2607.11520>
