# Universal log-rate of epidemic observables in a transport PDE SEIR model

**Model.** Let $n_E(x,t)$ and $n_I(x,t)$ be the densities of exposed and infectious individuals who entered their compartment $x$ time units ago. The time spent in a compartment is the transport variable. Transition hazards $K_{E\to I}(x)$ and $K_{I\to R}(x)$ depend on that time, so delays need not be exponential. Exposure has a maximal duration $x_E^*$ and infectiousness a maximal duration $x_I^*$. In the early, linear phase $S/N\approx1$, and with a constant contact intensity $\mu>0$ and infectiousness profile $\psi(x)$,

$$\begin{aligned}
&\partial_tn_E+\partial_xn_E+K_{E\to I}(x)\,n_E=0\ \ (0<x<x_E^*), && n_E(0,t)=\mu\int_0^{x_I^*}\psi(x)\,n_I(x,t)\,dx,\\
&\partial_tn_I+\partial_xn_I+K_{I\to R}(x)\,n_I=0\ \ (0<x<x_I^*), && n_I(0,t)=\int_0^{x_E^*}K_{E\to I}(x)\,n_E(x,t)\,dx+n_E(x_E^*,t).
\end{aligned}$$

Let $(S_t)_{t\ge0}$ be the solution semigroup on $L^1([0,x_E^*])\times L^1([0,x_I^*])$. An **epidemic observable**, such as daily emergency calls or hospital admissions, is any $Y_\kappa(t)=\int_0^{x_I^*}n_I(x,t)\,d\kappa(x)$ with $\kappa$ a nonnegative, nonzero Borel measure.

**Assumption.** $K_{E\to I}$ on $[0,x_E^*]$ and $\psi,K_{I\to R}$ on $[0,x_I^*]$ are nonnegative, measurable and bounded. $\psi$ is not a.e. zero, and $x_I^*$ is the right end of the essential support of $\psi$.

**Theorem.**

1. *(Perron–Frobenius eigenproblem.)* There is a pair $(\bar n,\lambda)$ with $\bar n=(\bar n_E,\bar n_I)$ continuous and positive and $\lambda\in\mathbb R$ such that $S_t\bar n=e^{\lambda t}\bar n$. Explicitly, $\bar n_E(x)=\bar n_E(0)\,e^{-\lambda x-\int_0^xK_{E\to I}}$ and $\bar n_I(x)=\bar n_I(0)\,e^{-\lambda x-\int_0^xK_{I\to R}}$, with the two boundary conditions closing the system. The eigenvalue is unique, and $\bar n$ is unique up to scaling.
2. *(Comparison.)* If $\alpha\bar n\le w\le\beta\bar n$ for some $\alpha,\beta>0$, then $\alpha e^{\lambda t}\bar n\le S_tw\le\beta e^{\lambda t}\bar n$ for all $t\ge0$.
3. *(Universality.)* If at some time $T$ the state is comparable to $\bar n$, that is $\alpha\bar n\le n(\cdot,T)\le\beta\bar n$, then for every observable $Y_\kappa$ the function $t\mapsto\log Y_\kappa(t)-\lambda t$ stays bounded. In particular

$$\lim_{t\to\infty}\frac1t\log Y_\kappa(t)=\lambda .$$

So all observables, whatever their reporting delay or detection profile $\kappa$, share the same exponential growth rate $\lambda$. This is why the growth rate of a single proxy, such as emergency calls, can monitor the epidemic in real time.

## Expansion

Along characteristics, the eigenfunction equations are linear ODEs in $x$, which gives the exponential profiles. Substituting into the boundary conditions leaves a scalar equation $\mu\,\Psi(\lambda)\,G(\lambda)=1$. Here $G(\lambda)=\int_0^{x_E^*}K_{E\to I}(x)e^{-\lambda x-\int_0^xK_{E\to I}}\,dx+e^{-\lambda x_E^*-\int_0^{x_E^*}K_{E\to I}}$ is the Laplace transform of the exposure-duration law, and $\Psi(\lambda)=\int_0^{x_I^*}\psi(x)e^{-\lambda x-\int_0^xK_{I\to R}}\,dx$. The left side is continuous and strictly decreasing from $+\infty$ to $0$ in $\lambda$, so $\lambda$ exists and is unique. This is the Euler–Lotka equation of the two-stage renewal process, with $\lambda>0$ iff the reproduction number $\mu\Psi(0)G(0)$ exceeds $1$. The comparison bound follows because $S_t$ is linear and order-preserving. Applying the positive linear form $\varphi=\kappa$ then bounds $Y_\kappa(t)$ between constant multiples of $e^{\lambda t}$.

These are the eigenvector proposition, the comparison lemma and the universality proposition of the source's transport-PDE section.

## Sources

- S. Gaubert, M. Akian, X. Allamigeon, M. Boyet et al., "Understanding and monitoring the evolution of the Covid-19 epidemic from medical emergency calls: the example of the Paris area", arXiv:2005.14186 (2020). <https://doi.org/10.48550/arXiv.2005.14186>
