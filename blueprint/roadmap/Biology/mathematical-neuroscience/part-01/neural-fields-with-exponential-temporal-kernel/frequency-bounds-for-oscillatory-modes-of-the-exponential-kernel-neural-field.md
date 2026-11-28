# Frequency bounds for oscillatory modes of the exponential-kernel neural field

**Setting.** For the neural field with exponential temporal kernel $\kappa(u)=\alpha e^{-\alpha u}$, leak $\tau$, transmission speed $\nu$ and connectivity $J$, linearized at the uniform equilibrium $v_0=\tau E$, let $\beta=\alpha c\tau F'(v_0)$, $D=|\beta|\int_{-\infty}^\infty|J(z)|\,dz$ and $L(\lambda)=\tau\lambda+1$. A neutral mode is a solution $w(x,t)=e^{i\omega t}e^{ikx}$, $\omega,k\in\mathbb R$, of the linearized equation, i.e. $\lambda=i\omega$ solves the dispersion relation $L(\lambda)=\beta\frac{\lambda}{\alpha+\lambda}\int J(z)e^{-\lambda|z|/\nu}e^{-ikz}dz$.

**Theorem.** Let $L$ be a polynomial whose roots have non-positive real parts. There is $B>0$, depending only on $L$ and $D$, such that every neutral mode has $|\omega|\le B$. If moreover $D<|L(0)|$, there is $A>0$ depending on $L$ and $D$ with $0<A\le|\omega|$ (for $L(\lambda)=\tau\lambda+1$ the condition is $D<1$, in which case there is no neutral mode at all). The source's (5.12) prints the lower bound under "$D<1$" for every such $L$; the page replaces this by $D<|L(0)|$, because for $L(\lambda)=\lambda$ and any $J$ with $D<1$ the value $\lambda=0$ solves the dispersion relation, so $w=e^{ikx}$ ($\omega=0$) is a neutral mode and no $A>0$ exists. Under $D<|L(0)|$ the bound holds: on a neutral mode $|L(i\omega)|\le D$, while $|L(i\omega)|>D$ for small $|\omega|$. For $L(\lambda)=\tau\lambda+1$,

$$\tau^2\omega^2\le D^2-1 .$$

## Expansion

On a neutral mode, $|L(i\omega)|\le|\beta|\,\big|\tfrac{i\omega}{\alpha+i\omega}\big|\int|J|\le D$, and $|L(i\omega)|\to\infty$ as $|\omega|\to\infty$, which gives $B$. For $L=\tau\lambda+1$ this reads $1+\tau^2\omega^2\le D^2$, so neutral modes, hence Hopf (uniform, $k=0$) and Turing–Hopf (travelling-wave, $k\ne0$) bifurcations, need $D>1$ and have bounded frequency; this is consistent with the $D<1$ stability criterion. The bound justifies truncating the delay factor $e^{-\lambda|z|/\nu}$ in a few-term expansion for fast transmission or rapidly decaying $J$, from which explicit Turing–Hopf conditions in the kernel rate $\alpha$, speed $\nu$, leak $\tau$ and excitatory-to-inhibitory range ratio follow.

## Depends on

- [No static bifurcations and a stability bound for the exponential-kernel neural field](no-static-bifurcations-and-stability-bound-for-the-exponential-kernel-neural-field.md)

## Sources

- E. Shamsara, M. E. Yamakou, F. M. Atay, J. Jost, "Dynamics of neural fields with exponential temporal kernel", *Theory in Biosciences* 143(2):107–122 (2024), Theorem 3 and equations (5.11)–(5.14), (5.21), <https://doi.org/10.1007/s12064-024-00414-7>, PMCID: PMC11127868.
