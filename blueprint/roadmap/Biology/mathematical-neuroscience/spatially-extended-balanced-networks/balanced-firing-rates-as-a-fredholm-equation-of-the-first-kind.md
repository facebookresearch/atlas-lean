# Balanced firing rates as a Fredholm equation of the first kind

**Model.** A network of $N$ neurons ($N_e=q_eN$ excitatory, $N_i=q_iN$ inhibitory) sits on a compact domain $\Omega$. A neuron at $x$ in population $a$ receives a synapse of strength $j_{ab}/\sqrt N$ from a neuron at $y$ in population $b$ with probability $p_{ab}(x,y)$ ($j_{ae}>0$, $j_{ai}<0$), plus feedforward input $\sqrt N\,F_a(x)$ with $F_a\in L^2(\Omega)$. With rates $\boldsymbol r=(r_e,r_i)$, the mean input is

$$\boldsymbol I=\sqrt N\,[\mathcal W\boldsymbol r+\boldsymbol F],\qquad(\mathcal W_{ab}r_b)(x)=\int_\Omega w_{ab}(x,y)\,r_b(y)\,dy,$$

with mean-field kernels $w_{ab}=p_{ab}j_{ab}q_b\in L^2(\Omega^2)$, so each $\mathcal W_{ab}$ is a compact Hilbert–Schmidt operator.

**Balance condition.** The network is balanced if $\|\boldsymbol r\|,\|\boldsymbol I\|$ stay $O(1)$ in $L^2(\Omega)$ as $N\to\infty$; then the $O(\sqrt N)$ excitation and inhibition cancel. Whatever the (nonlinear) input-to-rate map, any finite limit $\boldsymbol r_\infty$ must satisfy

$$\mathcal W\boldsymbol r_\infty+\boldsymbol F=0,$$

a linear Fredholm integral equation of the first kind. Because $\mathcal W$ is compact, there always exist input profiles $\boldsymbol F$ for which it has no solution: every spatially extended network is imbalanced by some inputs. Balance further requires the solution to be non-negative and stable.

**Finite-$N$ correction.** A rectified-linear rate approximation $r_a=g_a[I_a]_+$ with positive rates gives

$$\mathcal W\boldsymbol r+\boldsymbol F=\epsilon D\boldsymbol r,\qquad\epsilon=1/\sqrt N,\quad D=\operatorname{diag}(1/g_e,1/g_i),$$

an equation of the second kind that is generically solvable for every $\boldsymbol F$; its solution diverges as $\epsilon\to0$ exactly when the first-kind equation has none.

**Example.** On $\Omega=[0,1]$ with $p_{ab}(x,y)=12\bar p_{ab}(\min(x,y)-xy)$, the kernel $k(x,y)=\min(x,y)-xy$ has eigenvalues $\mu_m=1/(m^2\pi^2)$ and eigenfunctions $\sqrt2\sin(m\pi x)$. Balance holds iff the input coefficients $\tilde F_m$ make $\sum_m(\tilde F_m/\mu_m)\phi_m$ converge; for $F(x)=\sin(\pi x)$ the balanced rates are $\boldsymbol r(x)=-\overline W^{-1}\overline{\boldsymbol F}\,\pi^2\sin(\pi x)$, while inputs with $\tilde F_m/\mu_m\sim m^{-1}$ break balance.

## Expansion

Dividing the input equation by $\sqrt N$ shows $\mathcal W\boldsymbol r+\boldsymbol F=\boldsymbol I/\sqrt N\to0$ whenever $\boldsymbol I$ stays bounded. For a rate model $\tau\dot{\boldsymbol r}=-\boldsymbol r+g(\boldsymbol I)$ any fixed point satisfies $\mathcal W\boldsymbol r+\boldsymbol F=g^{-1}(\boldsymbol r)/\sqrt N$, which tends to the first-kind equation. Solvability of a first-kind equation with a compact operator requires the input's spectral coefficients to decay faster than the operator's eigenvalues, a Picard-type condition.

## Sources

- C. Ebsch, R. Rosenbaum, "Spatially extended balanced networks without translationally invariant connectivity", Journal of Mathematical Neuroscience 10 (2020), sections "Model and background", "Mean field theory of balance in spatially extended networks without translational invariance" and "Comparison of mean-field theory to spiking network simulations": Equations (1)–(10), (14), (16) and (18), <https://doi.org/10.1186/s13408-020-00085-w>, PMCID PMC7221049.
