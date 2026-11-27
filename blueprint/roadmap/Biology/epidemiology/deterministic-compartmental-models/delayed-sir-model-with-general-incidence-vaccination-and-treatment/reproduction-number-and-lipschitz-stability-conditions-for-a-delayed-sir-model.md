# Reproduction number and Lipschitz stability conditions for a delayed SIR model with vaccination and treatment

**Model.** Let $x, y, z$ be susceptible, infected and recovered numbers, with delays $\eta$ (vaccination), $\tau$ (infection) and $\delta$ (treatment):

$$\begin{aligned}
x' &= a - b f(x,y) - dx - c\,v(x(t-\eta)) + \alpha z,\\
y' &= b_1 f(x(t-\tau), y) - r\,p(y) - d_1 y,\\
z' &= r\,p(y(t-\delta)) - \alpha z,
\end{aligned}$$

with positive constants. The incidence $f$, vaccination $v$ and treatment $p$ are nonnegative and $C^1$, $f(0,y) = f(x,0) = 0$, $f$ is increasing in each argument, $v$ and $p$ are increasing, and they satisfy the Lipschitz bounds

$$|f(x,y) - f(\bar x,\bar y)| \le K_3|x-\bar x| + K_4|y-\bar y|,$$

$$M_1|x-\bar x| \le |v(x) - v(\bar x)| \le M_2|x-\bar x|, \qquad L_1|y-\bar y| \le |p(y) - p(\bar y)| \le L_2|y-\bar y|.$$

No lower bound of the same form can hold for $f$: since $f(0,y)=f(x,0)=0$, it would force both of its constants to vanish. Typical choices are $f = xy$, $xy/(1+bx)$, $xy/(1+ay)$, $p(y) = y$ or $y/(a+y)$, $v(x) = x$.

**Reproduction number.** With disease-free susceptible level $x^*$, the next-generation matrix is scalar and

$$R_0 = \frac{b_1 f_y(x^*, 0)}{r\,p'(0) + d_1}.$$

**Theorem (local stability of the disease-free equilibrium).** Since $f_x(x^*,0)=0$, the characteristic equation of the linearization at $(x^*,0,0)$, in the eigenvalue $\lambda\in\mathbb C$, factors as

$$\big(\lambda - b_1 f_y(x^*,0) + r p'(0) + d_1\big)\,(\lambda+\alpha)\,\big(\lambda + d + c\,v'(x^*)\,e^{-\lambda\eta}\big) = 0 .$$

If $R_0 > 1$ the disease-free equilibrium is unstable for all delays. If $R_0 < 1$ and either $\eta = 0$ or $c\,v'(x^*) < d$, every root has negative real part, so the disease-free equilibrium is locally asymptotically stable for all $\tau,\delta \ge 0$; the treatment delay $\delta$ does not enter.

**Theorem (global stability without delays).** Let $\eta=\tau=\delta=0$ and let $(x^*,y^*,z^*)$ be an endemic equilibrium. It is globally asymptotically stable among nonnegative solutions whenever

$$d + cM_1 - b_1K_3 > 0 \quad\text{and}\quad rL_1 - rL_2 + d_1 - (b + b_1)K_4 > 0.$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

There is a single infected compartment, so the reproduction number is the per-capita infection rate at the disease-free state, $b_1 f_y(x^*,0)$, divided by the per-capita removal rate $r p'(0) + d_1$. At the disease-free equilibrium the $y$-row of the linearization is $\big(0,\ b_1f_y(x^*,0)-rp'(0)-d_1,\ 0\big)$, so expanding along it splits off the factor $\lambda-b_1f_y(x^*,0)+rp'(0)+d_1$, whose root is negative exactly when $R_0<1$. The remaining $2\times2$ block is triangular, with roots $-\alpha$ and those of $\lambda+d+cv'(x^*)e^{-\lambda\eta}=0$. When $c\,v'(x^*)<d$ these lie in the left half-plane for every $\eta\ge0$; for $c\,v'(x^*)>d$ a pair crosses the imaginary axis at a finite $\eta$, whatever $R_0$.

For the global result take $U=|X|+|Y|+|Z|$ with $X=x-x^*$, $Y=y-y^*$, $Z=z-z^*$, and split $f(x,y)-f(x^*,y^*)=F_x+F_y$ with $F_x=f(x,y)-f(x^*,y)$ and $F_y=f(x^*,y)-f(x^*,y^*)$, which carry the signs of $X$ and $Y$. Using $-b\,\mathrm{sgn}(X)F_x=-b|F_x|$, $|F_x|\le K_3|X|$, $|F_y|\le K_4|Y|$, $|v(x)-v(x^*)|\ge M_1|X|$, $L_1|Y|\le|p(y)-p(y^*)|\le L_2|Y|$, and the cancellation of the $\alpha Z$ terms, the upper right Dini derivative satisfies

$$D^+U \le \big((b_1-b)^+K_3 - d - cM_1\big)|X| + \big((b+b_1)K_4 + rL_2 - rL_1 - d_1\big)|Y| .$$

Under the two inequalities $D^+U\le-\mu(|X|+|Y|)$ for some $\mu>0$, so $X,Y\to0$, and then $Z\to0$ from the $z$-equation. The source's Theorem 4.1 states its conditions with lower Lipschitz constants for $f$, which $f(0,y)=f(x,0)=0$ forces to be $0$, and with $+rL_2$, although its own Dini estimate gives $-rL_2$. Its Theorems 3.4–3.5 read the eigenvalues off a characteristic matrix as if it were triangular, which it is not at the endemic equilibrium, so the page states no endemic local criterion.

## Sources

- Sushil Pathak and Venkata Ratnam Kota, "An influential study of a time-delayed epidemic model incorporating vaccination and treatment interventions", *Advances in Continuous and Discrete Models* 2025 (2025), 57, <https://doi.org/10.1186/s13662-025-03920-0>. Preprint version: arXiv:2307.00339 (2023), model in Section 2, Section 3.3 ($R_0$), Theorem 3.4 (disease-free equilibrium, corrected here) and Theorem 4.1 (global stability without delays, corrected here), <https://doi.org/10.48550/arXiv.2307.00339>.
