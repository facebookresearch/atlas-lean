# Bistability and threshold manifold of the reduced Wolbachia invasion model

**Model.** Let $N(t)$ and $W(t)$ be the adult densities of wild and *Wolbachia*-carrying mosquitoes, assuming equal numbers of females and males in each class. The reduced model is

$$\frac{dN}{dt} = \rho_N N\frac{N}{N+W} - \alpha_N N - \beta_N N(N+W), \qquad \frac{dW}{dt} = \rho_W W - \alpha_W W - \beta_W W(N+W),$$

with positive fecundities $\rho_N, \rho_W$, mortalities $\alpha_N, \alpha_W$ and competition coefficients $\beta_N, \beta_W$. The factor $N/(N+W)$ encodes cytoplasmic incompatibility, since a wild female has viable offspring only with a wild male. Maternal transmission is encoded by the fact that $W$ is recruited only from $W$. Assume survival in isolation, $\rho_N > \alpha_N$ and $\rho_W > \alpha_W$, and set $N_\sharp = (\rho_N-\alpha_N)/\beta_N$ and $W_\sharp = (\rho_W-\alpha_W)/\beta_W$.

**Equilibria.** The equilibria are $E_0 = (0,0)$, $E_N = (N_\sharp, 0)$, $E_W = (0, W_\sharp)$ and, when $N_\sharp > W_\sharp$, the coexistence state $E_c = (N_c, W_c)$ with

$$W_c = W_\sharp\frac{\beta_N}{\rho_N}(N_\sharp - W_\sharp),\qquad N_c = W_\sharp - W_c .$$

**Theorem.** Assume $\rho_N > \alpha_N$, $\rho_W > \alpha_W$ and $N_\sharp > W_\sharp$.

1. The box $[0,N_\sharp]\times[0,W_\sharp]$ is positively invariant and absorbing, so the system is dissipative.
2. $E_N$ and $E_W$ are locally asymptotically stable, $E_c$ is unstable, and $E_0$ is a source.
3. The semiflow is monotone on $\mathbb{R}_+^2$, and strongly order-preserving on the interior, for the competitive order induced by the cone $\mathcal{K} = \mathbb{R}_+\times\mathbb{R}_-$: $(N_1,W_1) \le_{\mathcal{K}} (N_2,W_2)$ if and only if $N_1 \le N_2$ and $W_1 \ge W_2$.
4. Every initial state in the order interval between $E_c$ and $E_N$ other than $E_c$, that is $N_c \le N \le N_\sharp$ and $0 \le W \le W_c$, converges to $E_N$. Every initial state between $E_W$ and $E_c$ other than $E_c$ converges to $E_W$.
5. There is an invariant threshold manifold through $E_c$ separating the basins of attraction of $E_N$ and $E_W$, so the system has saddle-point behavior. A release of *Wolbachia* carriers succeeds exactly when it moves the state across this manifold.

## Expansion

With $Z = (N, -W)$ the system becomes cooperative, since its Jacobian $PJP$, $P = \operatorname{diag}(1,-1)$, is Metzler: both off-diagonal entries $N(\beta_N + \rho_N N/(N+W)^2)$ and $\beta_W W$ are nonnegative. Monotone dynamics in the plane then implies that the order interval between a stable boundary state and the unstable coexistence state is contained in that state's basin (Smith's theorem on order intervals bounded by equilibria). The stable manifold of the saddle $E_c$ is the separatrix. The condition $N_\sharp > W_\sharp$ means that *Wolbachia* lowers the carrying capacity, for example through reduced fecundity and increased mortality. It is what creates the frequency-dependent Allee effect behind threshold-based releases.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- D. Vicencio, O. Vasilieva and P. Gajardo, "Monotonicity properties arising in a simple model of Wolbachia invasion for wild mosquito populations", arXiv:2011.10501 (2020), Propositions 1–5 and Lemma 1, <https://doi.org/10.48550/arXiv.2011.10501>.
