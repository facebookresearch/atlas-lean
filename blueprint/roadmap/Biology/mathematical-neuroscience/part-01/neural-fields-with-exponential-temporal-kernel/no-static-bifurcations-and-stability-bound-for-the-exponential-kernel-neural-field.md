# No static bifurcations and a stability bound for the exponential-kernel neural field

**Model.** On $\Omega=\mathbb R$, the membrane activity $v(x,t)$ satisfies

$$v(x,t)=\int_{-\infty}^t\kappa(t-s)S(x,s)\,ds+\int_{-\infty}^t\Big(-\frac{v(x,s)}{\tau}+I_1(x,s)\Big)ds,\qquad S(x,t)=c\int_\Omega J(y-x)\,F\Big(v\big(y,t-\tfrac{|y-x|}{\nu}\big)\Big)dy+I_2(x,t),$$

with exponential temporal kernel $\kappa(u)=\alpha e^{-\alpha u}$ for $u\ge0$ (and $0$ for $u<0$; normalized, $\alpha>0$), leak time constant $\tau>0$, transmission speed $\nu>0$, even connectivity kernel $J$, smooth transfer function $F$, coupling $c>0$, and inputs $I_1,I_2$. For constant inputs $I_1\equiv E$, $I_2\equiv I_0$ the spatially uniform equilibrium is $v_0=\tau E$.

**Linearization.** Perturbations $w=e^{\lambda t}e^{ikx}$ of $v_0$ satisfy the dispersion relation

$$\tau\lambda+1=\beta\,\frac{\lambda}{\alpha+\lambda}\int_{-\infty}^{\infty}J(z)\,e^{-\lambda|z|/\nu}e^{-ikz}\,dz,\qquad \beta=\alpha c\tau F'(v_0).$$

**Theorem.**

1. The model admits no static bifurcation (saddle-node, pitchfork, or static Turing) from the uniform equilibrium $v_0$: $\lambda=0$ never solves the dispersion relation.
2. Let $D=|\beta|\int_{-\infty}^{\infty}|J(z)|\,dz$ and $L(\lambda)=\tau\lambda+1$. If $D<\min_{\omega\in\mathbb R}|L(i\omega)|$, then $v_0$ is locally asymptotically stable. In particular $D<1$ suffices.

## Expansion

At $\lambda=0$ the right-hand side vanishes because of the factor $\lambda/(\alpha+\lambda)$, while the left-hand side equals $1$; this factor is the trace of the derivative of the exponential kernel, so the field responds to changes of input rather than to constant levels. For stability, suppose a root $\lambda=\sigma+i\omega$ has $\sigma\ge0$. Then $|\lambda/(\alpha+\lambda)|<1$ and $|e^{-\lambda|z|/\nu}|\le1$, so $|L(\sigma+i\omega)|<D$. Since $L$ has its root in the left half-plane, $|L(i\omega)|\le|L(\sigma+i\omega)|$ for $\sigma\ge0$ (a lemma of Atay and Hutt), contradicting $D<\min_\omega|L(i\omega)|$. With $|L(i\omega)|^2=1+\tau^2\omega^2\ge1$, the condition $D<1$ is enough.

## Sources

- E. Shamsara, M. E. Yamakou, F. M. Atay, J. Jost, "Dynamics of neural fields with exponential temporal kernel", *Theory in Biosciences* 143(2):107–122 (2024), equations (2.1)–(2.3), (2.10), (3.6), (5.1), Theorem 1, Lemma 1, Theorem 2, <https://doi.org/10.1007/s12064-024-00414-7>, PMCID: PMC11127868.
