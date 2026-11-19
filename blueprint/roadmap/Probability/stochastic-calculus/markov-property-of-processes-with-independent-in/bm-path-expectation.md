# Time-dependent path expectation

Let $\mu$ be a measure on $\Omega$, let
$(B_t)_{t \ge 0}$ be a real process on $\Omega$ indexed by $t \in \mathbb{R}_{\ge 0}$, let
$s \ge 0$, and let $\nu_s$ be the law under $\mu$ (the pushforward of $\mu$) of the centered
shifted path $\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$. For a real function $Y$
on paths $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and $x \in \mathbb{R}$, the path expectation is the
Bochner integral $\int Y(t \mapsto x + f(t))\, d\nu_s(f)$, which is $0$ when the integrand is
not integrable.

This value can depend on $s$; it is the generic time-dependent expectation.
