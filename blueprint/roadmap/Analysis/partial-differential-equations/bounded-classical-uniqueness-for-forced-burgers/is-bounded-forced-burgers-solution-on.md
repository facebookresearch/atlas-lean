# Bounded forced Burgers solution class

For real $\nu,T$, a potential $q(t,x)$ and initial datum $u_0(x)$, the bounded solution class consists of real fields $u(t,x)$ with these properties:

- $u$ is jointly continuous on $[0,T]\times\mathbb R$.
- For each $t\in(0,T)$, the spatial slice $u(t,\cdot)$ is $C^2$.
- The ordinary time derivative $u_t(t,x)$ exists at every interior point and is jointly continuous on $(0,T)\times\mathbb R$.
- The actual derivatives satisfy $u_t(t,x)+u(t,x)u_x(t,x)=\nu u_{xx}(t,x)-2\nu q_x(t,x)$ for $0<t<T$.

- $u(0,x)=u_0(x)$ for every $x$.
- One constant $M\in\mathbb R$ satisfies $|u(t,x)|\le M$ throughout $[0,T]\times\mathbb R$.

There is no mixed or second time derivative requirement. This class contains the usual bounded classical $C^{1,2}$ solutions; joint continuity of the spatial derivatives is not needed here. No regularity is required outside the strip. The initial-value condition still applies independently of the sign of $T$.
