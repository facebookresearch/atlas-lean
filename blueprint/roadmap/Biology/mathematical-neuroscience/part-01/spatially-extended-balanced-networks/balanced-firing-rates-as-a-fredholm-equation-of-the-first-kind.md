# Balanced firing rates as a Fredholm equation of the first kind

**Model.** A network of $N$ neurons ($N_e=q_eN$ excitatory, $N_i=q_iN$ inhibitory) sits on a compact domain $\Omega$. A neuron at $x$ in population $a$ receives a synapse of strength $j_{ab}/\sqrt N$ from a neuron at $y$ in population $b$ with probability $p_{ab}(x,y)$ ($j_{ae}>0$, $j_{ai}<0$), plus feedforward input $\sqrt N\,F_a(x)$ with $F_a\in L^2(\Omega)$. With rates $\boldsymbol r=(r_e,r_i)$, the mean input is

$$\boldsymbol I=\sqrt N\,[\mathcal W\boldsymbol r+\boldsymbol F],\qquad(\mathcal W_{ab}r_b)(x)=\int_\Omega w_{ab}(x,y)\,r_b(y)\,dy,$$

with mean-field kernels $w_{ab}=p_{ab}j_{ab}q_b\in L^2(\Omega^2)$, so each $\mathcal W_{ab}$ is a compact Hilbert–Schmidt operator.

**Balance condition.** The network is balanced if $\|\boldsymbol r\|,\|\boldsymbol I\|$ stay $O(1)$ in $L^2(\Omega)$ as $N\to\infty$; then the $O(\sqrt N)$ excitation and inhibition cancel. Whatever the (nonlinear) input-to-rate map, any finite limit $\boldsymbol r_\infty$ must satisfy

$$\mathcal W\boldsymbol r_\infty+\boldsymbol F=0,$$

a linear Fredholm integral equation of the first kind. Because $\mathcal W$ is compact, there always exist input profiles $\boldsymbol F$ for which it has no solution: every spatially extended network is imbalanced by some inputs. Balance further requires the solution to be non-negative and stable.

**Finite-$N$ correction.** A rectified-linear rate approximation $r_a=g_a[I_a]_+$ with positive rates gives

$$\mathcal W\boldsymbol r+\boldsymbol F=\epsilon D\boldsymbol r,\qquad\epsilon=1/\sqrt N,\quad D=\operatorname{diag}(1/g_e,1/g_i),$$

an equation of the second kind that is generically solvable for every $\boldsymbol F$; its solution $\boldsymbol r_\epsilon$ is unbounded in $L^2$ as $\epsilon\to0$ whenever the first-kind equation has no solution in $L^2$.

**Example.** On $\Omega=[0,1]$ with $p_{ab}(x,y)=12\bar p_{ab}(\min(x,y)-xy)$, the kernel $k(x,y)=\min(x,y)-xy$ has eigenvalues $\mu_m=1/(m^2\pi^2)$ and eigenfunctions $\sqrt2\sin(m\pi x)$. With $\phi_m(x)=\sqrt2\sin(m\pi x)$ orthonormal and $\tilde F_m=\langle F,\phi_m\rangle$, the first-kind equation has a solution in $L^2$ iff the Picard condition $\sum_m|\tilde F_m/\mu_m|^2<\infty$ holds, and for separable inputs $F_a=\bar F_aF$ the solution is then $-\overline W^{-1}\overline{\boldsymbol F}\sum_m(\tilde F_m/\mu_m)\phi_m$; balance further needs it non-negative. For $F(x)=\sin(\pi x)$ the balanced rates are $\boldsymbol r(x)=-\overline W^{-1}\overline{\boldsymbol F}\,\pi^2\sin(\pi x)$, while an input with $\tilde F_m=m^{-5/2}$, which lies in $L^2$, has $|\tilde F_m/\mu_m|^2=\pi^4/m$ with divergent sum and so breaks balance.

## Expansion

If $\boldsymbol r_\epsilon$ stayed bounded along a sequence $\epsilon\to0$, a weakly convergent subsequence would have a limit $\boldsymbol r$ with $\mathcal W\boldsymbol r_\epsilon\to\mathcal W\boldsymbol r$ in norm ($\mathcal W$ is compact) and $\epsilon D\boldsymbol r_\epsilon\to0$, so $\mathcal W\boldsymbol r+\boldsymbol F=0$; this gives the divergence statement. The converse can fail: in the separable case, if $D^{-1}\overline W$ has a positive eigenvalue $\theta$, the mode-$m$ matrix $\epsilon D-\mu_m\overline W$ is singular at $\epsilon=\theta\mu_m\to0$, so $\boldsymbol r_\epsilon$ is unbounded as $\epsilon\to0$ even when a balanced solution exists. Dividing the input equation by $\sqrt N$ shows $\mathcal W\boldsymbol r+\boldsymbol F=\boldsymbol I/\sqrt N\to0$ whenever $\boldsymbol I$ stays bounded. For a rate model $\tau\dot{\boldsymbol r}=-\boldsymbol r+g(\boldsymbol I)$ any fixed point satisfies $\mathcal W\boldsymbol r+\boldsymbol F=g^{-1}(\boldsymbol r)/\sqrt N$, which tends to the first-kind equation. Solvability of a first-kind equation with a compact operator is the Picard condition: in the shared-eigenbasis setting of the companion expansion, $\sum_m\|\widetilde W_m^{-1}\widetilde{\boldsymbol F}_m\|^2<\infty$, which in the separable case reads $\sum_m|\tilde F_m/\mu_m|^2<\infty$.

## Sources

- C. Ebsch, R. Rosenbaum, "Spatially extended balanced networks without translationally invariant connectivity", Journal of Mathematical Neuroscience 10 (2020), sections "Model and background", "Mean field theory of balance in spatially extended networks without translational invariance" and "Comparison of mean-field theory to spiking network simulations": Equations (1)–(10), (14), (16) and (18), Theorem 1 and Corollary 1 (Eq. (12), the separable solution), <https://doi.org/10.1186/s13408-020-00085-w>, PMCID PMC7221049.
