# Large-population limit of the spectrum of a killed birth–death process

**Model.** For a carrying-capacity parameter $K\in\mathbb{Z}_{>0}$, let $(X^{(K)}_t)$ be a birth–death process on $\{0,1,2,\dots\}$ with rates

$$\lambda^{(K)}_n=K\,b(n/K),\qquad \mu^{(K)}_n=K\,d(n/K),$$

with $b(0)=d(0)=0$, so that $0$ (extinction) is absorbing and reached almost surely. The fluid limit of $X^{(K)}/K$ on finite time intervals solves $\dot x=b(x)-d(x)$.

**Assumptions.** $b(x)/x$ and $d(x)/x$ are positive, twice differentiable and increasing; $b(x)/d(x)\to0$ as $x\to\infty$; $b'(0)>d'(0)>0$ (so $0$ is a repelling fixed point); there is a unique $x_*>0$ with $b(x_*)=d(x_*)$, and $b'(x_*)\neq d'(x_*)$ (then $b'(x_*)<d'(x_*)$, so $x_*$ is attracting); plus the technical conditions $\int_{x_*/2}^\infty dx/d(x)<\infty$, $\sup_x(d'(x)/d(x)-1/x)<\infty$, $\log(d/b)$ increasing, $H(x)=\int_{x_*}^x\log\frac{d(s)}{b(s)}ds$ three times differentiable with $\sup_x(1+x^2)|H'''(x)|<\infty$, and $\log b(x)/x,\ \log d(x)/x\to0$ as $x\to\infty$. The logistic process $b(x)=\lambda x$, $d(x)=x(\mu+x)$ with $\lambda>\mu>0$ satisfies them, with $x_*=\lambda-\mu$.

**Killed generator.** On sequences indexed by $n\ge1$,

$$(L_Kv)(n)=\lambda^{(K)}_n\big(v(n+1)-v(n)\big)+\mu^{(K)}_n\big(v(n-1)\mathbf{1}_{\{n>1\}}-v(n)\big).$$

With $\pi^{(K)}_1=1/\mu^{(K)}_1$ and $\pi^{(K)}_n=\lambda^{(K)}_1\cdots\lambda^{(K)}_{n-1}/(\mu^{(K)}_1\cdots\mu^{(K)}_n)$, the closure of $L_K$ in $\ell^2(\pi^{(K)})$ is self-adjoint with compact resolvent; its spectrum consists of simple eigenvalues $-\rho^{(K)}_0>-\rho^{(K)}_1>\cdots$, all negative. The quasi-stationary distribution is $\nu^{(K)}(n)\propto\pi^{(K)}_n\psi^{(K)}_0(n)$, where $\psi^{(K)}_0$ is the first eigenvector, and $\mathbb{P}_{\nu^{(K)}}(T_0>t)=e^{-\rho^{(K)}_0t}$, with $\rho^{(K)}_0$ exponentially small in $K$.

**Theorem (convergence of the spectrum).** Let

$$S_1=\big(d'(x_*)-b'(x_*)\big)\,\mathbb{Z}_{\ge0},\qquad S_2=\big(b'(0)-d'(0)\big)\,\mathbb{Z}_{>0},$$

and let $0=\eta_0\le\eta_1\le\eta_2\le\cdots$ enumerate $S_1\cup S_2$ in nondecreasing order, with each value in $S_1\cap S_2$ listed twice. Then for every $j\ge0$,

$$\lim_{K\to\infty}\rho^{(K)}_j=\eta_j .$$

$S_1$ is the spectrum (up to sign) of the Ornstein–Uhlenbeck generator $b(x_*)f''+(b'(x_*)-d'(x_*))xf'$ describing fluctuations of size $\sqrt K$ around $Kx_*$; $S_2$ is that of a linear binary branching process with birth rate $b'(0)$ and death rate $d'(0)$, killed at $0$, describing the dynamics near extinction. For the logistic process the two sets coincide away from $0$, giving asymptotically double eigenvalues.

## Expansion

Taylor expansion of the rates at $n=Kx_*+\sqrt K\,y$ turns $L_K$ acting on $u((n-Kx_*)/\sqrt K)$ into the Ornstein–Uhlenbeck generator up to $O(K^{-1/2})$, whose eigenvalues are $-k(d'(x_*)-b'(x_*))$ with Hermite eigenfunctions. Near $n=1$, the rates are $n\,b'(0)+O(n^2/K)$ and $n\,d'(0)+O(n^2/K)$, so $L_K$ is within $O(1/K)$ of the generator of the killed linear birth–death process, whose spectrum in its own weighted $\ell^2$ space is $-k(b'(0)-d'(0))$, $k\ge1$. The two limits live at different scales and in different function spaces, so the proof works with eigenvectors: quasi-eigenvectors built from each limit show every point of $S_1\cup S_2$ is a limit of eigenvalues (with multiplicity), and a splitting of each eigenvector of $L_K$ into a piece localized near $1$ and a piece localized near $Kx_*$, plus compactness (Fréchet–Kolmogorov–Riesz) for each piece, shows there are no other limits.

## Sources

- J. -r. Chazottes, P. Collet and S. Méléard, "Large population limit of the spectrum of killed birth-and-death processes", Journal of Functional Analysis 285 (2023), 110092, <https://doi.org/10.1016/j.jfa.2023.110092>; numbering as in arXiv:2204.10748: Section 2 (standing assumptions) and Theorem 1.2.
