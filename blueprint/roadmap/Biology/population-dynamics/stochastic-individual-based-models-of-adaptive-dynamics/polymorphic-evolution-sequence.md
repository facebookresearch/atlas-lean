# Polymorphic evolution sequence

**Model.** Fix a trait space $\mathcal{X}$ and a carrying-capacity parameter $K \in \mathbb{N}$. Each individual with trait $x$ gives birth at rate $b(x) \ge 0$; the offspring is a mutant with probability $p(x)$ (or $u_K p(x)$ when mutation probabilities are scaled with $K$), its trait then drawn from a mutation kernel $m(x,dy)$, and otherwise a clone. Each individual dies at the natural rate $d(x) \ge 0$ plus a competition rate $\frac1K \sum_j c(x, x_j)$ summed over the other individuals. The rescaled population is the finite point measure $\nu^K_t = \frac1K \sum_{i=1}^{N_t} \delta_{x_i(t)} \in \mathcal{M}_F(\mathcal{X})$. For a monomorphic population of trait $x$ with $b(x)>d(x)$ the logistic equilibrium is $\bar n(x) = (b(x)-d(x))/c(x,x)$, and the *invasion fitness* of a mutant $y$ against coexisting residents $\mathbf{x}=(x_1,\dots,x_d)$ at equilibrium $\bar n(\mathbf{x})$ is $f(y,\mathbf{x}) = b(y) - d(y) - \sum_{i} c(y,x_i)\, \bar n_{x_i}(\mathbf{x})$.

**Coexistence.** Two traits $x, y$ coexist if and only if $f(x,y) > 0$ and $f(y,x) > 0$, or $f(x,y)=f(y,x)=0$.

**Theorem (Champagnat–Méléard).** Suppose that for every set of coexisting traits the Lotka–Volterra system started with an invading mutant converges to a unique stable equilibrium $\bar n^*$. Let $x_1,\dots,x_d$ coexist, let $\nu^K_0 \to \sum_i \bar n_{x_i}(\mathbf{x})\,\delta_{x_i}$ almost surely, and let the mutation probability $u_K$ satisfy
$$e^{-VK} \ll u_K \ll \frac{1}{K \ln K} \qquad \text{for all } V>0 .$$
Then $(\nu^K_{t/(K u_K)})_{t \ge 0}$ converges in finite-dimensional distributions to the pure-jump measure-valued process $\Lambda$, the *polymorphic evolution sequence*, with $\Lambda_0 = \sum_{x \in \mathbf{x}} \bar n_x(\mathbf{x})\delta_x$, which jumps from $\sum_{x \in \mathbf{x}} \bar n_x(\mathbf{x})\delta_x$ to $\sum_{x \in \mathbf{x}\cup\{y\}} \bar n^*_x(\mathbf{x}\cup\{y\})\delta_x$ at rate
$$\sum_{x \in \mathbf{x}} p(x)\, b(x)\, \bar n_x(\mathbf{x})\, \frac{[f(y,\mathbf{x})]_+}{b(y)}\, m(x,dy).$$
When only monomorphic states are visited this reduces to the trait substitution sequence.

## Depends on

- [Large-population limit of the birth–death–competition process](large-population-limit-of-the-birth-death-competition-process.md)

## Expansion

Mutants appear at rate $K u_K \sum_x p(x) b(x) \bar n_x$; each founds a near-linear birth–death process with birth rate $b(y)$ and growth rate $f(y,\mathbf{x})$, which survives with probability $[f(y,\mathbf{x})]_+/b(y)$. A successful invasion takes time $O(\ln K)$, so $u_K \ll 1/(K\ln K)$ separates the mutation and invasion time scales, while $u_K \gg e^{-VK}$ prevents the residents from dying out by a large deviation before the next mutation.

## Sources

- A. Bovier, A. Kraut, "Stochastic individual-based models", arXiv:2607.11520, Proposition 3.5 (coexistence criterion) and Theorem 5.2 (polymorphic evolution sequence). <https://doi.org/10.48550/arXiv.2607.11520>
