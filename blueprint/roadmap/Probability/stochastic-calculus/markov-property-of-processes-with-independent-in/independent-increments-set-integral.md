# Bounded integrals of future path functionals over present events

Let $\mu$ be a
probability measure on $\Omega$, let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration indexed by
$\mathbb{R}_{\ge 0}$, and let $(B_t)_{t \ge 0}$ be a real-valued process that is adapted (each
$B_t$ is $\mathcal{F}_t$-measurable) and has independent increments (for $u \le t$, the
increment $B_t - B_u$ is independent of $\mathcal{F}_u$ under $\mu$). Fix $s \ge 0$ and let
$\nu_s$ be the law under $\mu$ of the centered shifted path
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$ on $\mathbb{R}^{\mathbb{R}_{\ge 0}}$
with the product σ-algebra. Let $Y : \mathbb{R}^{\mathbb{R}_{\ge 0}} \to \mathbb{R}$ be
measurable with $|Y(p)| \le C$ for every path $p$, for some real $C$, and for $x \in \mathbb{R}$
put $\Phi_s(x) = \int Y(t \mapsto x + f(t)) \, d\nu_s(f)$. Then for every $A \in \mathcal{F}_s$,

$$\int_A Y\big((B_{s+t}(\omega))_{t \ge 0}\big) \, d\mu(\omega)
= \int_A \Phi_s(B_s(\omega)) \, d\mu(\omega).$$
