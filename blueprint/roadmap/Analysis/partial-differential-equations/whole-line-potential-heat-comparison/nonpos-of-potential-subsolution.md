# Nonpositivity of potential-heat subsolutions

Let $\nu\ge0$ and $T\in\mathbb R$. Every field considered is jointly continuous on
$[0,T]\times\mathbb R$, has $C^2$ spatial slices at every $0<t<T$, and has an actual
ordinary time derivative there, denoted by its subscript $t$. Neither spatial
regularity at time zero nor a time derivative at either endpoint is assumed.
Each field $w$ has uniform exponential strip growth: there are constants
$M,c\ge0$, allowed to differ between fields, with
$|w(t,x)|\le M e^{c|x|}$ for all $0\le t\le T$ and all $x\in\mathbb R$.

The potential $q$ satisfies $q(t,x)\le K$ for a single finite real $K$ on
$(0,T)\times\mathbb R$. No continuity, differentiability, or lower bound for $q$
is required. Write

$$
\mathcal L_q w=w_t-\nu\partial_x^2w-qw.
$$

Here $\partial_x^2w$ is the actual twice-iterated ordinary derivative. Fields
and sources may have either sign.

If $\mathcal L_q u\le0$ at interior times and $u(0,x)\le0$ for every $x$, then
$u(t,x)\le0$ on the whole closed strip. Set $L=\max(K,0)$ and multiply $u$ by
$e^{-Lt}$. Only at a positive value of this transformed field does its heat
residual have to be nonpositive; at such a point $u>0$ and $q\le L$ gives the
required sign. The positive-set maximum principle applies on smaller horizons,
and continuity supplies $t=T$. This does not assume $qu\le0$ for negative $u$.

## Sources

The maximum-principle background is Stanford Math 220B, [*Heat Equation*](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf), Theorems 18 and 20, and James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.8. The exponential spatial barrier and exponential time factor derive the stated whole-line potential results; these references are not asserted to state exactly this linear-exponential growth class and endpoint formulation.
