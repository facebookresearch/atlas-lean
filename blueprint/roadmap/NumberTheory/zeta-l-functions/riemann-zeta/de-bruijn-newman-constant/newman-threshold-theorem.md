# Newman's threshold theorem for the de Bruijn–Newman deformation

There is a real number $\Lambda \le 1/2$ such that, for every real $\lambda$, all zeros of the de
Bruijn–Newman deformation

$$
H_\lambda(z) = \int_0^\infty e^{\lambda u^2} \Phi(u) \cos(z u) \, du
$$

are real if and only if $\lambda \ge \Lambda$. Thus the set of times $\lambda$ at which all zeros of
$H_\lambda$ are real is the closed half-line $[\Lambda, \infty)$, and $\Lambda$ is its infimum, the
de Bruijn–Newman constant.

The theorem strengthens two earlier results recalled by Rodgers and Tao: if all zeros of
$H_\lambda$ are real, then so are all zeros of $H_{\lambda'}$ for every $\lambda' > \lambda$
(Pólya), and all zeros of $H_\lambda$ are real for $\lambda \ge 1/2$ (de Bruijn).

With the [criterion](riemann-hypothesis-iff-zeros-all-real.md) that the Riemann hypothesis holds
exactly when all zeros of $H_0$ are real, and the [theorem of Rodgers and
Tao](rodgers-tao-negative-time-wanted.md) that $H_\lambda$ has a non-real zero for every
$\lambda < 0$, the Riemann hypothesis implies $\Lambda = 0$. The converse, that $\Lambda = 0$ implies the Riemann
hypothesis, needs the attainment of the threshold given here: $\Lambda = 0$ then makes all zeros of
$H_0$ real.

## Depends on

- [Real-rootedness of the de Bruijn–Newman deformation](zeros-all-real.md)
- [The de Bruijn–Newman constant](de-bruijn-newman-constant.md)

## Sources

- B. Rodgers and T. Tao, *The de Bruijn–Newman constant is non-negative*, Forum Math. Pi 8 (2020), e6, arXiv:1801.05914v3, §1: "Newman [17] showed that there is an absolute constant $-\infty < \Lambda \le 1/2$, now known as the De Bruijn–Newman constant, with the property that $H_t$ has purely real zeroes if and only if $t \ge \Lambda$", after recalling the results of Pólya and de Bruijn above; [17] is C. M. Newman, *Fourier transforms with only real zeros*, Proc. Amer. Math. Soc. 61 (1976), 245–251.
