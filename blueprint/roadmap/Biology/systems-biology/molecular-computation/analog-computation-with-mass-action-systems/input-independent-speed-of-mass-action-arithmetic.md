# Input-independent speed of mass-action arithmetic

**Speed.** If $g:\mathbb R_{\ge0}\to\mathbb R$ converges to $g^*$, its *rate of convergence* is $\rho=-\limsup_{t\to\infty}t^{-1}\ln|g(t)-g^*|\in(0,\infty]$, and $g$ *computes $g^*$ at speed $\rho$* (Definition in Section 3). If $|g(t)-g^*|\le ct^me^{-\rho t}$ for all $t$, the rate is at least $\rho$. If $T_n$ is the first time after which $g$ is correct to $n$ decimal places, then $n\ln 10/T_n\to\rho$.

**Input dependence and its removal (Section 2.3).** With all rate constants equal to 1, the network $0\to X$, $A+X\to A$ gives $\dot x=1-ax$ and computes $1/a$ at speed $a$, which degrades for small inputs. The autocatalytic network $X\to2X$, $A+2X\to A+X$ gives $\dot x=x(1-ax)$ and computes $1/a$ at speed $1$ for every $a>0$ and $x(0)>0$.

**Elementary modules (Section 4).** Let the inputs $a(t),b(t)\ge0$ converge to $a^*,b^*$ at rates at least $\rho_a,\rho_b$. Then, for example:
- Addition: $A\to A+X$, $B\to B+X$, $X\to0$, i.e. $\dot x=a+b-x$, computes $a^*+b^*$ at speed at least $\min\{\rho_a,\rho_b,1\}$.
- $m$th root ($m\ge2$): $Y\to2Y$, $A+(m+1)Y\to A+mY$, $X\to2X$, $Y+2X\to Y+X$, i.e. $\dot y=y(1-ay^m)$, $\dot x=x(1-yx)$, computes $\sqrt[m]{a^*}$ at speed at least $\min\{\rho_a,1\}$ if $a^*\ne0$ and $\min\{\rho_a/m,1\}$ if $a^*=0$.
- Similar modules compute identification, inversion, multiplication, absolute difference, rectified subtraction and partial real inversion, each at speed at least $\min\{\text{input rates},1\}$.

**Theorem 5.1 (composite computations).** A computation composed of finitely many elementary modules, wired so that outputs of one feed inputs of the next and all run simultaneously, has speed at least that of its slowest elementary computation.

**Corollaries 5.2–5.3.** If no step takes a root of zero, the composite speed is at least $1$; if $p$ steps take $m_j$-th roots of zero, it is at least $\prod_{j=1}^p 1/m_j$. The number of steps does not affect the asymptotic speed.

## Expansion

Each module is a scalar non-autonomous ODE of the form $\dot x=g_1(t)x^k-g_2(t)x^{k+1}$ or $\dot x=g_1(t)-g_2(t)x$ whose coefficients converge exponentially; the convergence lemmas of Section 3 show that $x$ converges at the minimum of the coefficients' rates and the linearized rate at the attracting equilibrium. Autocatalysis normalizes that linearized rate: for $\dot x=x(1-ax)$ the Jacobian at $x^*=1/a$ is $1-2ax^*=-1$, independent of $a$. Composition follows by induction along the computation graph, since a module's input rate is the rate of its upstream module. A root of zero converges only polynomially in the inner variable's distance, which divides the rate by $m$. Scaling all rate constants by $\sigma$ multiplies every speed by $\sigma$.

## Sources

- D. F. Anderson, B. Joshi, "Chemical mass-action systems as analog computers: implementing arithmetic computations at specified speed", *Theoretical Computer Science* 1025 (2025), 114983, speed definition and convergence lemma of Section 3, elementary-operation lemmas of Section 4, Theorem 5.1 and Corollaries 5.2–5.3, <https://doi.org/10.1016/j.tcs.2024.114983> (preprint arXiv:2404.04396).
