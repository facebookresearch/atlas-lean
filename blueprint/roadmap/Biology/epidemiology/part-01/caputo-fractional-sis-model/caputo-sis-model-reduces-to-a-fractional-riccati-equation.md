# Caputo fractional SIS model reduces to a fractional Riccati equation

**Model.** In a population of constant size $N$, with contact rate $\beta>0$, recovery rate $\gamma>0$ and infected death rate $e>0$ (deaths replaced by susceptible newborns), the Caputo fractional SIS model of order $\alpha\in(0,1)$ is

$$D_{0,t}^{\alpha}S=-\frac{\beta}{N}SI+(e+\gamma)I,\qquad D_{0,t}^{\alpha}I=\frac{\beta}{N}SI-(e+\gamma)I,\qquad (S(0),I(0))=(N-I_0,I_0).$$

**Statement.**

(1) *Reduction.* $D^\alpha_{0,t}(S+I)=0$, so $S+I\equiv N$, and the infected class solves the fractional Riccati (logistic) equation

$$D_{0,t}^{\alpha}I=c\,I-\frac{\beta}{N}I^2,\qquad I(0)=I_0,\qquad c=\beta-(e+\gamma).$$

(2) *Well-posedness.* The right-hand side $f(I)=cI-\frac{\beta}{N}I^2$ is locally Lipschitz, so on a box $[0,b]\times[I_0-\delta,I_0+\delta]$ there is a unique solution on $[0,b^*]$ with $b^*=\min\{b,(\delta\,\Gamma(\alpha+1)/\|f\|_\infty)^{1/\alpha}\}$. The constant states $I\equiv0$ and, for $c\ne0$, $I\equiv cN/\beta$ are solutions, and by uniqueness the solution from $I_0=cN/\beta$ stays there.

(3) *Variational iteration.* With $d=-\beta/N$, the iteration $I_{n+1}=I_n-D_{0,t}^{-\alpha}\big(D_{0,t}^{\alpha}I_n-cI_n-dI_n^2\big)$, $I_0(t)\equiv I_0$, produces polynomials in $t^\alpha$; the first step is $I_1(t)=I_0+\frac{cI_0+dI_0^2}{\Gamma(\alpha+1)}t^\alpha$. For $\alpha\to1$ the iterates reproduce the Taylor expansion of the classical logistic solution

$$I(t)=\frac{cI_0}{\frac{\beta}{N}I_0+\big(c-\frac{\beta}{N}I_0\big)e^{-ct}}\quad(c\ne0),\qquad I(t)=\frac{I_0}{1+\beta I_0t/N}\quad(c=0).$$

(4) *Isolated infecteds.* If $\beta=0$ the equation is linear, $D^\alpha_{0,t}I=-(e+\gamma)I$, and the iteration sums exactly to $I(t)=I_0\,E_{\alpha}\!\big(-(e+\gamma)t^{\alpha}\big)$, a Mittag-Leffler decay; as the source notes, the smaller $\alpha$, the more time the infection takes to vanish.

## Expansion

Adding the two equations and using $D^\alpha_{0,t}\,\mathrm{const}=0$ together with $D^{-\alpha}_{0,t}D^\alpha_{0,t}h=h-h(0)$ for $0<\alpha<1$ gives conservation of $N$; substituting $S=N-I$ yields the Riccati equation. Well-posedness is the standard local existence and uniqueness theorem for Caputo initial value problems applied to a $C^1$ right-hand side, whose derivative $c+2dI$ is bounded on compact sets. In the linear case the iteration generates $\sum_k(-(e+\gamma)t^\alpha)^k/\Gamma(\alpha k+1)$ term by term. The source also implements the explicit fractional Euler (product-rectangle) scheme $y_{n+1}=y_0+h^\alpha\sum_{j=0}^n b_{j,n+1}f(t_j,y_j)$ with $b_{j,n+1}=[(n-j+1)^\alpha-(n-j)^\alpha]/\Gamma(\alpha+1)$ and reports agreement with the iterates; smaller $\alpha$ lengthens the time to eradication.

## Depends on

- [SIS infected class satisfies the logistic equation](../../sis-epidemic-model/sis-infected-eq-logistic.md)

## Sources

- Hassouna M, Ouhadan A, El Kinani EH. On the solution of fractional order SIS epidemic model. *Chaos, Solitons and Fractals* (2018). <https://doi.org/10.1016/j.chaos.2018.10.023> (PMCID: PMC7125670). Eqs. (14)-(17), Theorems 1-2, iterations (27)-(33), Remark 2 (Eqs. (34)-(35)), Euler scheme (40)-(41).
