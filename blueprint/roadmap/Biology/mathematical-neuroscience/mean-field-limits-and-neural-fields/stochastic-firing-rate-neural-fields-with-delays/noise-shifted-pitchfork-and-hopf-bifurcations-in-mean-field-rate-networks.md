# Noise-shifted pitchfork and Hopf bifurcations in mean-field rate networks

**Model.** $P$ populations of noisy firing-rate neurons: neuron $i$ in population $\alpha$ obeys

$$
dV^i_t=\Big(-\frac{V^i_t}{\tau_\alpha}+I_\alpha(t)+\sum_{\beta=1}^P\frac{J_{\alpha\beta}}{N_\beta}\sum_{j:\,p(j)=\beta}S_\beta(V^j_t)\Big)dt+\lambda_\alpha(t)\,dB^i_t ,
$$

with $N_\alpha/N\to\delta_\alpha\in(0,1)$ and Lipschitz sigmoids $S_\beta$ valued in $[0,1]$. As $N\to\infty$ (Touboul–Hermann–Faugeras, Theorem 1.1) each neuron converges to the McKean–Vlasov process $d\bar V^\alpha=\big[-\bar V^\alpha/\tau_\alpha+I_\alpha+\sum_\beta J_{\alpha\beta}\mathbb{E}[S_\beta(\bar V^\beta)]\big]dt+\lambda_\alpha dB^\alpha$: for every $T>0$ there is $C(T)$ with $\sup_{0\le t\le T}\mathbb E|V^i_t-\bar V^i_t|\le C(T)/\sqrt N$, and propagation of chaos holds. The constant can be taken independent of $T$ when $\tau_M\max_\alpha\sum_\beta|J_{\alpha\beta}|L_\beta<1$, with $\tau_M=\max_\alpha\tau_\alpha$ and $L_\beta$ the Lipschitz constant of $S_\beta$. For Gaussian initial data (Proposition 1.2) the solution stays Gaussian with mean $\mu_\alpha$ and variance $v_\alpha$ solving

$$
\dot\mu_\alpha=-\frac{\mu_\alpha}{\tau_\alpha}+\sum_\beta J_{\alpha\beta}f_\beta(\mu_\beta,v_\beta)+I_\alpha,\qquad \dot v_\alpha=-\frac{2v_\alpha}{\tau_\alpha}+\lambda_\alpha^2,
$$

and for $S_\alpha(x)=\Phi(g_\alpha x+\gamma_\alpha)$, with $\Phi$ the standard Gaussian distribution function, $f_\alpha(\mu,v)=\Phi\big((g_\alpha\mu+\gamma_\alpha)/\sqrt{1+g_\alpha^2v}\big)$ (Lemma 1.3). The variance decouples and relaxes to $\tau_\alpha\lambda_\alpha^2/2$, so noise acts only by lowering the effective slope $g_\alpha\mapsto g_\alpha/\sqrt{1+g_\alpha^2v_\alpha}$.

**Proposition (pitchfork; Touboul–Hermann–Faugeras, Proposition 2.1).** One population, $\tau=1$, $\gamma=0$, $S(x)=\Phi(gx)$, $I=-J/2$, constant noise $\lambda$. In the deterministic finite network the null state is stable if $J<0$ or $gJ<\sqrt{2\pi}$, unstable for $J>0$, $g>g_c:=\sqrt{2\pi}/J$, with a pitchfork at $g_c$. In the stochastic mean-field limit the pitchfork moves to

$$
g^*=\frac{\sqrt{2\pi}}{\sqrt{J^2-\pi\lambda^2}}>g_c\qquad(J>0,\ \lambda<J/\sqrt\pi),
$$

and the null mean state $\mu=0$ is stable if $J<0$, or $J>0$ and $\lambda>J/\sqrt\pi$ (large noise), or $J>0$, $\lambda<J/\sqrt\pi$ and $g<g^*$; it is unstable when $J>0$, $\lambda<J/\sqrt\pi$ and $g>g^*$.

**Proposition (Hopf; Proposition 2.2).** Two equal-size populations (excitatory $1$, inhibitory $2$) with common $\tau,g,\lambda$, connectivity $J\frac{2}{N}\begin{pmatrix}1&-1\\1&1\end{pmatrix}$ and inputs $I_1=0$, $I_2=-J$. The deterministic network has a supercritical Hopf bifurcation of the null state at $g_c=\sqrt{2\pi}/J$ (Jacobian eigenvalues $-1+\frac{gJ}{\sqrt{2\pi}}(1\pm i)$, the rest $-1$). In the mean-field limit the Hopf point moves to the same $g^*$, and for $\lambda>J/\sqrt\pi$ the null state is stable for every gain: sufficiently strong noise destroys the oscillations.

## Depends on

- [Gaussian moment equations of the stochastic firing-rate neural field](gaussian-moment-equations-of-the-stochastic-firing-rate-neural-field.md)

## Proof sketch

At $\mu=0$ the linearization of the mean equation has slope $Jg/\sqrt{2\pi(1+g^2\lambda^2/2)}$, using the stationary variance $\lambda^2/2$. Setting it equal to $1$ gives $g^2(J^2-\pi\lambda^2)=2\pi$, hence $g^*$; when $\pi\lambda^2\ge J^2$ the slope stays below $1$ for all $g$. Noise therefore stabilizes a state that is unstable without noise even in this effectively one-dimensional equation. The mean-field prediction describes the finite network on bounded time intervals; the Gronwall bound $M_t\le K\int_0^te^{-(t-s)/\tau}M_s\,ds+K'/\sqrt N$ on $M_t=\mathbb E|V^i_t-\bar V^i_t|$ is uniform in $t$ only when $K\tau<1$.

## Sources

- Jonathan Touboul, Geoffroy Hermann and Olivier Faugeras, "Noise-Induced Behaviors in Neural Mean Field Dynamics", *SIAM Journal on Applied Dynamical Systems* 11 (2012), 49–81, <https://doi.org/10.1137/110832392>. Preprint version: arXiv:1104.5425 (2011), <https://doi.org/10.48550/arXiv.1104.5425>.
