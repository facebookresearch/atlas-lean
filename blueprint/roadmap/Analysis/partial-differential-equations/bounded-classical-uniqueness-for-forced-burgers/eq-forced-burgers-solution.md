# Uniqueness of bounded forced Burgers solutions

Assume $\nu>0$ and $T\ge0$. The potential has $C^2$ spatial slices at every time in $[0,T]$. For each $k=0,1,2$, the actual spatial derivative $\partial_x^kq$ is jointly continuous on $[0,T]\times\mathbb R$ and has a uniform bound there:

$$\forall k\le2\quad\exists C_k\in\mathbb R\quad\forall(t,x)\in[0,T]\times\mathbb R,\quad |\partial_x^kq(t,x)|\le C_k.$$

No time derivative of $q$ is assumed.

For real $\nu,T$, a potential $q(t,x)$ and initial datum $u_0(x)$, the bounded solution class consists of real fields $u(t,x)$ with these properties:

- $u$ is jointly continuous on $[0,T]\times\mathbb R$.
- For each $t\in(0,T)$, the spatial slice $u(t,\cdot)$ is $C^2$.
- The ordinary time derivative $u_t(t,x)$ exists at every interior point and is jointly continuous on $(0,T)\times\mathbb R$.
- The actual derivatives satisfy $u_t(t,x)+u(t,x)u_x(t,x)=\nu u_{xx}(t,x)-2\nu q_x(t,x)$ for $0<t<T$.

- $u(0,x)=u_0(x)$ for every $x$.
- One constant $M\in\mathbb R$ satisfies $|u(t,x)|\le M$ throughout $[0,T]\times\mathbb R$.

There is no mixed or second time derivative requirement. This class contains the usual bounded classical $C^{1,2}$ solutions; joint continuity of the spatial derivatives is not needed here. No regularity is required outside the strip. The initial-value condition still applies independently of the sign of $T$.

For an arbitrary spatial anchor $a$, define

$$g_a(x)=\exp\left(-\frac1{2\nu}\int_a^x u_0(y)\,dy\right).$$

Let $\Phi_a$ be the actual potential-heat Volterra evolution of $g_a$, and set

$$U_a(t,x)=-2\nu\frac{\partial_x\Phi_a(t,x)}{\Phi_a(t,x)}.$$

Every $u$ in this class satisfies

$$u(t,x)=U_a(t,x)\qquad(0\le t\le T,\ x\in\mathbb R).$$

The initial datum is automatically bounded and continuous. Equality of the inverse profiles on each entire spatial slice gives equality of their spatial derivatives; the logarithmic derivative recovers the velocity. This also works at initial and terminal times, without endpoint time derivatives. Values outside the strip are unrestricted and no equality there is asserted.

The transform background is Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Theorem 3.3 and Remark 3.4. Uniqueness uses whole-line potential-heat comparison for profiles with uniform exponential growth.
