# Coexistence-invasion fronts of Lotka–Volterra competition with a slow diffuser

Consider the two-species Lotka–Volterra competition–diffusion system
$$u_t=u_{xx}+u(1-u-rv),\qquad v_t=\varepsilon v_{xx}+\ell v(1-su-v),\qquad x\in\mathbb R,$$
with $r<1$, $\ell>0$, a small diffusion rate $0<\varepsilon\ll1$ for $v$ and a small competition coefficient $s=O(\varepsilon)$. The coexistence state is $(u^*_\varepsilon,v^*_\varepsilon)=\big(\frac{1-r}{1-rs},\frac{1-s}{1-rs}\big)=(1-r,1)+O(\varepsilon)$. An $(e_4,e_1)$-wave is a solution $(u,v)=(U,V)(x-ct)$ with $(U,V)(-\infty)=(u^*_\varepsilon,v^*_\varepsilon)$ and $(U,V)(+\infty)=(0,0)$, that is, a front along which both species jointly invade empty space.

**Theorem.** Assume $r<1$ and $s=O(\varepsilon)$. For all sufficiently small $\varepsilon>0$:

1. (Existence) $(e_4,e_1)$-waves exist for every speed $c>2$.
2. (Monotonicity and uniqueness) both components of each such wave are strictly decreasing, and for each $c$ the wave is unique up to translation.
3. (Stability in exponentially weighted spaces) Let $C_\omega=\{\varphi\in C_0:(1+e^{\delta z})\varphi(z)\in C_0\}$.
   - If $\ell>2$ and $4<c^2\le\ell^2/(\ell-1)$, the essential spectrum in $C_\omega$ meets the right half-plane for every $\delta>0$, and the wave is unstable in $C_\omega$ for all $\delta>0$ (absolute instability).
   - If $\ell\le2$ and $c>2$, or $\ell>2$ and $c^2>\ell^2/(\ell-1)$, the wave is asymptotically stable with no shift in $C_\omega$ for every $\delta>0$ with $\delta^2-c\delta+1<0$ and $\varepsilon\delta^2-c\delta+\ell<0$.

## Expansion

In the moving frame $z=x-ct$ the profile equations form a four-dimensional system with fast variables $(u,u')$ and slow variables $(v,v')$, because $v$ diffuses at rate $\varepsilon$. For $\varepsilon=0$ the $v$-equation reduces to a first-order logistic flow along a critical manifold, and the $u$-equation is a Fisher–KPP equation whose minimal speed is $2$. Fenichel theory persists the slow manifold, and transversality of the singular heteroclinic connection gives true fronts for each $c>2$. Linearizing at $e_1=(0,0)$ in the frame gives continuous spectrum $\{-\xi^2+ic\xi+1\}$ for $u$ and $\{-\varepsilon\xi^2+ic\xi+\ell\}$ for $v$. A weight $e^{\delta z}$ shifts these to $\delta^2-c\delta+1$ and $\varepsilon\delta^2-c\delta+\ell$, which explains both inequalities; when $\ell>2$ and $c^2\le\ell^2/(\ell-1)$ no weight moves the $v$-branch left. The point spectrum is handled by approximating the Evans function with its singular limit $E_1$, all of whose zeros are real and negative.

## Sources

- Chueh-Hsin Chang, Tzi-Sheng Yang, "Existence and Asymptotic Stability of Traveling Waves of Two-species Lotka-Volterra Competition-Diffusion Systems via Geometric Singular Perturbations", arXiv:2609.16624 (2026), Section 2 (system and equilibria), Theorem 2.1, Theorem 3.1, Proposition 4.1, Proposition 5.1 and Theorem 5.1, <https://doi.org/10.48550/arXiv.2609.16624>.
