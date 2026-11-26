# Gene frequency spectrum under horizontal gene transfer

**Model (infinitely many genes with horizontal gene flow).** A population of $N$ bacterial cells evolves in discrete Wright–Fisher generations: each cell of generation $t+1$ picks a parent uniformly from generation $t$. The accessory genome of a cell is a finite set of genes drawn from a continuum gene pool $I$. To form a child's genome:

1. **gene loss:** each gene of the parent is kept independently with probability $1 - \rho/(2N)$;
2. **gene gain:** new genes are added as a Poisson process on $I$ with intensity $\theta/(2N)$, so every gained gene is new;
3. **horizontal gene transfer:** for every donor cell $i$ and every gene $v$ that $i$ carries, $v$ is added to the child with probability $\gamma/(2N^3)$ (no effect if already present).

Here $\rho > 0$, $\theta > 0$ and $\gamma \ge 0$. With time measured in units of $N$ generations, the frequency $X$ of a single gene converges as $N \to \infty$ to the diffusion

$$dX = \Big( -\frac{\rho}{2} X + \frac{\gamma}{2} X(1-X) \Big)\,dt + \sqrt{X(1-X)}\,dW,$$

in which transfer acts like positive selection of strength $\gamma$, because its rate is proportional to the number $N^2 X(1-X)$ of donor–acceptor pairs.

For a sample of $n$ cells, the **gene frequency spectrum** $G^{(n)}_k$, $1 \le k \le n$, is the number of genes carried by exactly $k$ sampled cells.

**Theorem (Baumdicker–Pfaffelhuber, Theorem 1).** In equilibrium, as $N \to \infty$,

$$E\big[G^{(n)}_k\big] = \frac{\theta}{k} \cdot \frac{n(n-1)\cdots(n-k+1)}{(n-1+\rho)(n-2+\rho)\cdots(n-k+\rho)} \Big( 1 + \sum_{m=1}^{\infty} \frac{(k)_m\,\gamma^m}{(n+\rho)_m\, m!} \Big),$$

where $(a)_b = a(a+1)\cdots(a+b-1)$. Equivalently,

$$E\big[G^{(n)}_k\big] = \theta \binom{n}{k} (k-1)!\, \frac{\Gamma(n-k+\rho)}{\Gamma(n+\rho)}\; {}_1F_1(k; n+\rho; \gamma).$$

At $\gamma = 0$ the hypergeometric factor equals $1$ and the spectrum reduces to that of the model without transfer; every expected value is continuous at $\gamma = 0$. Large $\gamma$ pushes genes to high frequency, so most genes are shared by most cells (a closed pangenome).

## Depends on

- [Expected site frequency spectrum under the Poisson random field model](../diffusion-theory/poisson-random-field-model/expected-sfs.md)

## Expansion

For the diffusion with drift $b(x) = -\tfrac12\rho x + \tfrac12\gamma x(1-x)$ and variance $a(x) = x(1-x)$, the scale density is $\psi(y) = \exp(-2\int_0^y b/a) = (1-y)^{1-\rho} e^{-\gamma y}$. New genes enter at frequency $\delta$ at rate $\frac{\theta}{2}\frac{1}{\phi(\delta)}$ with $\phi(x) = \int_0^x \psi$, and the Green function $G(\delta,x) = 2\phi(\delta)/(a(x)\psi(x))$ gives the time spent at frequency $x$ before loss. In equilibrium the number of genes at frequency in $dx$ is therefore Poisson with mean density

$$\theta\, \frac{e^{\gamma x}}{x(1-x)^{1-\rho}},$$

independent of $\delta$. Sampling $n$ cells binomially gives $E[G^{(n)}_k] = \binom nk \int_0^1 \theta\, e^{\gamma x} x^{k-1}(1-x)^{n-k-1+\rho}\,dx$, and Kummer's integral representation of ${}_1F_1$ yields the formula.

## Sources

- F. Baumdicker and P. Pfaffelhuber, *Evolution of bacterial genomes under horizontal gene transfer*, arXiv:1105.5014 (2011). <https://doi.org/10.48550/arXiv.1105.5014>
