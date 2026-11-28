# Foliation of the GnRH regulating system by the surge-to-pulse duration ratio

**Setting.** In the FitzHugh–Nagumo-based model of the gonadotropin-releasing hormone (GnRH) pulse and surge generator, a slow *regulating system* drives a faster *secreting system*; the sign of the regulating variable $X$ decides between pulsatile phases and surges. In the fast time, the regulating system $(RS_\varepsilon)$ is the slow–fast system

$$\dot X=-Y+g(X),\qquad \dot Y=\varepsilon\,(X+b_1Y+b_2),\qquad g(X)=-X^3+3\mu^2X,$$

with $0<\varepsilon\ll1$, $\mu>0$, $b_1>0$. The cubic $Y=g(X)$ has a local minimum at $X=-\mu$ and a local maximum at $X=\mu$.

**Bifurcation surfaces.** The middle equilibrium crosses the fold at $X_0=-\mu$ on the supercritical Hopf surface

$$\mathcal H_p:\ b_2=h_p(b_1)=\mu+2\mu^3b_1 .$$

Near $\varepsilon=0$, for $b_1\in\big(\frac{\mu+\alpha}{4\mu^3},\frac1{\mu^2}\big)$, there is a $C^1$ surface of homoclinic connections to the left saddle

$$\mathcal H_c:\ b_2=h_c(b_1,\varepsilon)=2\mu-2\mu^3b_1+O(\varepsilon^{2/3}).$$

For fixed $\alpha>0$, if $b_2<\mu+2\mu^3b_1-\alpha$ and $b_2<2\mu-2\mu^3b_1$, then for all small $\varepsilon$ the system has an attracting relaxation limit cycle $C(b_1,b_2,\varepsilon)$ that visits $\{X\ge\mu\}$ and lies in an $O(\varepsilon^{2/3})$ neighbourhood of its singular limit. Let $\mathcal R_1=\{b_2<h_p(b_1)-\alpha,\ b_2<h_c(b_1,\varepsilon),\ \varepsilon<\varepsilon_0\}$.

**Theorem.** Parametrize $C(b_1,b_2,\varepsilon)$ with $X(0)=0$, $Y(0)>0$, period $T$. There is a unique $T_-\in(0,T)$ with $X\le0$ on $[0,T_-]$ and $X\ge0$ on $[T_-,T]$; set $T_+=T-T_-$ (the time spent with $X>0$, which sets the surge duration). Then there exists, near $\varepsilon=0$, a $C^1$ foliation of $\mathcal R_1$ by two-dimensional leaves such that

1. each leaf is a graph $b_2=l_r(b_1,\varepsilon)$, $b_1\in[\bar b_1^{\,r},1/\mu^2)$, of a differentiable function $l_r$;
2. for each $r\ge1$ there is a leaf on which

$$\frac{T_-(b_1,b_2,\varepsilon)}{T_+(b_1,b_2,\varepsilon)}=r .$$

At $\varepsilon=0$ the leaves reduce to one-dimensional curves $b_2=l^0_r(b_1)$ in the $(b_1,b_2)$ plane with the singular ratio $T^0_-/T^0_+=r$.

## Expansion

In the singular limit the relaxation cycle consists of two slow segments on the outer branches of the cubic, joined by fast jumps at the folds $X=\pm\mu$. The slow flow $\dot X\,g'(X)=X+b_1g(X)+b_2$ gives each phase duration as an explicit integral, $T^0_\pm$, that depends smoothly and monotonically on $b_2$; the implicit function theorem turns the level sets of $T^0_-/T^0_+$ into $C^1$ curves. For $\varepsilon>0$, the trajectories stay $O(\varepsilon^{2/3})$ close to the singular cycle (Fenichel and blow-up estimates near the folds), so the durations are $C^1$ perturbations and the curves extend to surfaces. The leaf index $r$ is the ratio of pulsatile-phase to surge duration, which is how the model's parameters are tuned to the observed ovarian-cycle specifications.

## Proof depends on

- [Implicit function theorem](../../../Analysis/real-functions/multivariable-calculus/implicit-function-theorem.md)

## Sources

- Frédérique Clément, Alexandre Vidal, "Bifurcation-based parameter tuning in a model of the GnRH pulse and surge generator", arXiv:0809.1722 (2008), Section 3 (Lemma 3.1, Proposition 3.1, Hopf surface and the domain $\mathcal R_1$) and Section 4 (Lemma 4.1, Proposition 4.1, Theorem 4.1), <https://doi.org/10.48550/arXiv.0809.1722>.
