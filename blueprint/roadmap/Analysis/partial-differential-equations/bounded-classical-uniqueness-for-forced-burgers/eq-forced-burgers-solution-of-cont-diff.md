# Smooth-potential specialization of bounded uniqueness

Assume $\nu>0$, $T\ge0$, and $q:\mathbb R^2\to\mathbb R$ is jointly $C^\infty$. Assume a bound for every Frechet derivative order, uniform on the closed strip:

$$\forall n\ge0\quad\exists C_n\in\mathbb R\quad\forall(t,x)\in[0,T]\times\mathbb R,\quad \|D^nq(t,x)\|\le C_n.$$

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

Every $u$ in this class equals $U_a$ throughout the closed strip. The smooth-potential hypotheses imply the finite spatial derivative conditions needed for profile identification. The competitor still needs only the weaker regularity stated in its class, and its initial datum is automatically bounded and continuous. No mixed or second time derivative of the competitor is introduced.
