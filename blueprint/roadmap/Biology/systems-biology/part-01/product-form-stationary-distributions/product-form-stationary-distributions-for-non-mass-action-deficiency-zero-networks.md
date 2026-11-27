# Product-form stationary distributions for non-mass-action deficiency zero networks

**Stochastic model.** A reaction network on species $S_1, \dots, S_d$ has reactions
$\nu_k \to \nu_k'$, $k = 1, \dots, K$, with complexes $\nu_k, \nu_k' \in \mathbb{Z}^d_{\ge 0}$. It is
modelled as a continuous-time Markov chain on $\mathbb{Z}^d_{\ge 0}$ that jumps from $x$ to
$x + \nu_k' - \nu_k$ at rate $\lambda_k(x)$. The associated deterministic mass-action system is
$\dot x = \sum_k \kappa_k x^{\nu_k} (\nu_k' - \nu_k)$, and $c \in \mathbb{R}^d_{>0}$ is a
**complex-balanced equilibrium** if for every complex $\eta$,
$\sum_{k : \nu_k = \eta} \kappa_k c^{\nu_k} = \sum_{k : \nu_k' = \eta} \kappa_k c^{\nu_k}$.

**Anderson–Craciun–Kurtz form.** If $\lambda_k(x) = \kappa_k \prod_{i=1}^{d}\prod_{j=0}^{\nu_{ki} - 1}
\theta_i(x_i - j)$ with $\theta_i(0) = 0$ (mass action is $\theta_i(z) = z$) and the mass-action
system has a complex-balanced equilibrium $c$, then

$$\pi(x) = \prod_{i=1}^{d} \frac{c_i^{x_i}}{\prod_{j=0}^{x_i - 1} \theta_i(x_i - j)}$$

is a stationary measure, normalizable whenever it is summable.

**Assumption (stoichiometric divisibility).** Partition the species into $\mathcal{S}_1 \cup
\mathcal{S}_2$, where $S_i \in \mathcal{S}_2$ iff $\alpha_i = \gcd\{\nu_{1i}, \dots, \nu_{Ki}\} > 1$,
and set $\alpha_i = 1$ for $S_i \in \mathcal{S}_1$. The intensities have the form

$$\lambda_k(x) = \kappa_k \prod_{i=1}^{d} \prod_{j=0}^{\nu_{ki}/\alpha_i - 1} \theta_i(x_i - j\alpha_i),
\qquad \theta_i(z) = 0 \ \text{for } z \le \alpha_i - 1,$$

with $\theta_i(z) > 0$ for $z \ge \alpha_i$; species consumed only in multiples of $\alpha_i$ may thus
have any rate function of their own count evaluated in steps of $\alpha_i$.

**Theorem.** Under this assumption, if for some rate constants $\kappa$ the deterministic mass-action
system admits a complex-balanced equilibrium $c \in \mathbb{R}^d_{>0}$ (for example, when the network
is weakly reversible with deficiency zero), the stochastic model has the stationary measure

$$\pi(x) = \prod_{i=1}^{d} \frac{c_i^{x_i}}{\prod_{j=0}^{\lfloor x_i/\alpha_i \rfloor - 1} \theta_i(x_i - j\alpha_i)},$$

which can be normalized to a stationary distribution whenever it is summable.

## Depends on

- [Anderson–Craciun–Kurtz on a finite class](../../stochastic-mass-action-metabolic-control-and-flu/poisson-weight-vec-mul-class-generator.md)

## Expansion

The proof reduces to the Anderson–Craciun–Kurtz form by factoring each $\theta_i$ for
$S_i \in \mathcal{S}_2$ as $\theta_i(z) = \varphi_i(z)\varphi_i(z-1)\cdots\varphi_i(z - \alpha_i + 1)$,
with $\varphi_i(0) = 0$, $\varphi_i(z) = 1$ for $1 \le z \le \alpha_i - 1$, and
$\varphi_i(z) = \theta_i(z)/(\varphi_i(z-1)\cdots\varphi_i(z-\alpha_i+1))$ recursively for
$z \ge \alpha_i$. Because $\alpha_i$ divides every $\nu_{ki}$, each block of $\alpha_i$ consecutive
factors in the intensity is exactly one $\theta_i$, so $\lambda_k(x) = \kappa_k \prod_i
\prod_{b=0}^{\nu_{ki}-1}\varphi_i(x_i - b)$, and an induction on $x_i$ shows
$\prod_{j=0}^{x_i-1}\varphi_i(x_i - j) = \prod_{j=0}^{\lfloor x_i/\alpha_i\rfloor - 1}\theta_i(x_i -
j\alpha_i)$. The setting arises from stochastic averaging and quasi-equilibrium reductions, where
eliminating a fast species produces effective non-mass-action propensities for slow ones, such as a
dimerization $2P \rightleftharpoons D$ with effective propensities for $P$; the theorem then gives the
invariant distribution of the fast subsystem in closed form, avoiding a numerical solve of the
master equation.

## Sources

- D. F. Anderson, S. L. Cotter, "Product-form stationary distributions for deficiency zero networks
  with non-mass action kinetics", Bulletin of Mathematical Biology 78 (2016), Eq. (6),
  Theorem 1, Assumption 1 with Eq. (8), Theorem 2 and its proof,
  <https://doi.org/10.1007/s11538-016-0220-y> (PMC5104833).
- D. F. Anderson, G. Craciun, T. G. Kurtz, "Product-form stationary distributions for deficiency
  zero chemical reaction networks", Bulletin of Mathematical Biology 72 (2010) 1947-1970,
  <https://doi.org/10.1007/s11538-010-9517-4>.
