# Li–Muldowney second-compound criterion

Let $\dot x=f(x)$ with $f\in C^1(D)$, $D\subset\mathbb{R}^n$ open and simply connected, and $x(t,x_0)$ the solution with $x(0,x_0)=x_0$. Assume

- **(H1)** $D$ contains a compact absorbing set $K$;
- **(H2)** the system has a unique equilibrium $x^*$ in $D$.

Let $J^{[2]}$ be the second additive compound of the Jacobian $J=Df$; for $n=3$ and $J=(a_{ij})$,

$$
J^{[2]}=\begin{pmatrix}a_{11}+a_{22}&a_{23}&-a_{13}\\ a_{32}&a_{11}+a_{33}&a_{12}\\ -a_{31}&a_{21}&a_{22}+a_{33}\end{pmatrix}.
$$

Let $P(x)$ be a $C^1$ nonsingular $\binom n2\times\binom n2$ matrix function, $P_f$ its derivative along $f$, $B=P_fP^{-1}+PJ^{[2]}P^{-1}$, and $\mu$ a Lozinskii measure for some vector norm. If

$$
\bar q_2=\limsup_{t\to\infty}\ \sup_{x_0\in K}\ \frac1t\int_0^t\mu\big(B(x(s,x_0))\big)\,ds<0,
$$

then $x^*$ is globally asymptotically stable in $D$.

The source applies this to the SIQ model

$$
\dot S=\Lambda-\gamma SI-d_0S,\qquad \dot I=\gamma SI-(d_0+k+\eta)I+\sigma Q,\qquad \dot Q=\eta I-(d_0+\mu+\sigma)Q,
$$

whose basic reproduction number is $R_0=\dfrac{\Lambda\gamma(d_0+\mu+\sigma)}{d_0\big[(d_0+k)(d_0+\mu+\sigma)+\eta(d_0+\mu)\big]}$. For $R_0>1$ the endemic equilibrium $E_2^*$ is the unique interior equilibrium and $\Omega=\{S+I+Q\le\Lambda/d_0\}$ is absorbing; with $P=(S/I)\,\mathrm{Id}_3$ and the norm $\|(X_1,X_2,X_3)\|=\max\{|X_1|,|X_2|+|X_3|\}$ the source's estimate gives $\bar q_2\le-2d_0<0$ under $\mu+\sigma>\eta$, so $E_2^*$ is globally asymptotically stable (Theorem 3).

## Expansion

The second compound governs the evolution of two-dimensional surface elements: $\bar q_2<0$ means that the flow contracts area uniformly in the time average. By a Bendixson-type argument this rules out periodic orbits, homoclinic loops and heteroclinic cycles; combined with the closing lemma and (H1)–(H2), every omega-limit set reduces to $x^*$. Unlike a Lyapunov function, the method needs no candidate function, only a good choice of $P$ and norm; for epidemic models (H2) is usually arranged by restricting $D$ to the interior where $R_0>1$ makes the disease-free equilibrium repelling (uniform persistence).

## Sources

- A. Din, Y. Li, T. Khan, G. Zaman, "Mathematical analysis of spread and control of the novel corona virus (COVID-19) in China", *Chaos, Solitons & Fractals* 141 (2020) 110286. <https://doi.org/10.1016/j.chaos.2020.110286>. PMCID: PMC7510499. (Model (1), Theorem 3.)
- M. Y. Li, J. S. Muldowney, "A geometric approach to global-stability problems", *SIAM Journal on Mathematical Analysis* 27 (1996) 1070–1083. <https://doi.org/10.1137/S0036141094266449>
