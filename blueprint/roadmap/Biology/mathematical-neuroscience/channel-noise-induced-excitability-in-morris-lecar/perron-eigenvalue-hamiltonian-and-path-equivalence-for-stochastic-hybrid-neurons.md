# Perron-eigenvalue Hamiltonian and path equivalence for stochastic hybrid neurons

**Model.** In the Morris–Lecar neuron with $N$ two-state sodium channels and $M$ two-state potassium channels, with $n$ and $m$ open,

$$
\frac{dv}{dt}=\frac nNf_{\mathrm{Na}}(v)+\frac mMf_{\mathrm K}(v)+f_{\mathrm L}(v)+I_{\mathrm{app}},
$$

and each channel opens and closes with voltage-dependent rates ($\beta_ia_i(v)$ closed$\to$open, $\beta_ib_i(v)$ open$\to$closed, $i=\mathrm{Na},\mathrm K$), so $(v,m,n)$ is a piecewise deterministic (stochastic hybrid) Markov process whose density solves a Chapman–Kolmogorov equation. With fast sodium gating $\beta_{\mathrm{Na}}^{-1}=O(\epsilon)$ and many potassium channels $M^{-1}=O(\epsilon)$, the deterministic Morris–Lecar model is recovered as $\epsilon\to0$, and rare events are governed by a stationary density of WKB form

$$
p_s(n,\mathbf x)\sim\mathcal N\bigl[r_0(n\mid\mathbf x)+\epsilon r_1(n\mid\mathbf x)\bigr]k(\mathbf x)\,e^{-W(\mathbf x)/\epsilon},\qquad \mathbf x=(v,\ m/M),
$$

with quasipotential $W$ solving the Hamilton–Jacobi equation $\mathcal H(\mathbf x,\nabla W)=0$. At leading order $r_0(\cdot\mid\mathbf x)$ is the positive null vector of the matrix $\mathbb M(\mathbf p)=A+D(\mathbf p)$, where $A$ is the generator of the sodium-channel birth–death chain and $D(\mathbf p)$ is diagonal (voltage drift times $p_v$ plus the potassium contribution).

**Lemma (Perron eigenvalue).** Let $A$ be an irreducible transition-rate matrix (nonnegative off-diagonal entries, zero column sums) and $D(\mathbf p)$ diagonal, smooth in $\mathbf p$, with $D(0)=0$. For each fixed $\mathbf p$, $A+D(\mathbf p)$ has a positive eigenvector $q$ (all entries positive), unique up to a positive scalar factor, so unique under the normalisation $\sum_iq_i=1$; every positive eigenvector spans this one ray. Its eigenvalue $\mathcal H(\mathbf p)$ is real and simple and exceeds the real part of every other eigenvalue. $\mathcal H$ is the Hamiltonian of the large deviation principle, whose characteristics $\dot{\mathbf x}=\nabla_{\mathbf p}\mathcal H$, $\dot{\mathbf p}=-\nabla_{\mathbf x}\mathcal H$ on $\mathcal H=0$ are the most probable paths.

**Theorem (path equivalence).** Let $\widehat{\mathcal H}(\mathbf x,\mathbf p)=\tau^{-1}\det\bigl(A+D(\mathbf p)\bigr)$ for a constant $\tau\ne0$. For initial data $(\mathbf x_0,\mathbf p_0)$ with $\mathcal H=\widehat{\mathcal H}=0$, if both Hamiltonian systems have unique bounded continuous solutions on $(0,T)$ and $(0,\hat T)$, there is a continuous one-to-one time change $\zeta:(0,\hat T)\to(0,T)$ with $(\hat{\mathbf x}(s),\hat{\mathbf p}(s))=(\mathbf x(\zeta(s)),\mathbf p(\zeta(s)))$. Hence the explicit determinant Hamiltonian yields the same most probable paths and quasipotential as the implicitly defined Perron eigenvalue.

## Expansion

Adding $\kappa I$ makes $A+D(\mathbf p)+\kappa I$ nonnegative and irreducible, so the Perron–Frobenius theorem gives a simple dominant eigenvalue with a one-dimensional eigenspace spanned by a positive vector (one positive ray), and no other eigenvalue has a nonnegative eigenvector, shifted back by $\kappa$. Since $\det(A+D)$ is the product of all eigenvalues and the Perron eigenvalue is simple, the zero sets $\{\mathcal H=0\}$ and $\{\widehat{\mathcal H}=0\}$ coincide near the relevant paths, and on this common level set $\nabla\widehat{\mathcal H}=c(\mathbf x,\mathbf p)\nabla\mathcal H$ with $c$ the product of the other eigenvalues divided by $\tau$, which has constant sign; the two Hamiltonian flows therefore trace the same curves at speeds differing by $c$, giving the time change $\zeta$. For two-state sodium channels the ansatz $q(n)=A^n/(n!(N-n)!)$ makes $\widehat{\mathcal H}$ explicit. Computing $W$ by an ordered upwind method shows that in both type I and type II Morris–Lecar neurons, channel noise produces spontaneous spikes by the same mechanism: escape paths cross a threshold curve near which potassium fluctuations dominate.

## Sources

- J. M. Newby, "Spontaneous excitability in the Morris–Lecar model with ion channel noise", arXiv:1406.2914 (2014), Section 2 (stochastic hybrid model), Section 3 (WKB approximation, Eqs. for $\mathbb M(\mathbf p)$ and $\mathcal H$) and appendix "Establishing path equivalence" (Perron–Frobenius lemma and path-equivalence theorem), <https://doi.org/10.48550/arXiv.1406.2914>.
- Published version: J. M. Newby, "Spontaneous Excitability in the Morris–Lecar Model with Ion Channel Noise", SIAM Journal on Applied Dynamical Systems 13 (2014), 1756–1791, <https://doi.org/10.1137/140971385>.
