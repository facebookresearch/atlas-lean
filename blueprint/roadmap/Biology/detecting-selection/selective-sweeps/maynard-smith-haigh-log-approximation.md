# Logarithmic approximation of hitchhiking at a tightly linked neutral locus

In the [haploid hitchhiking model](maynard-smith-haigh-exact-hitchhiking-recursion.md), replace the recursions by the differential equations

$$\dot p = s p (1 - p), \qquad \dot Q = c (1 - p)(R - Q), \qquad \dot R = c\, p\, (Q - R),$$

with $Q(0) = 0$, $R(0) = R_0$. Then $Q - R = -R_0 e^{-ct}$, and

$$\frac{dQ}{dp} = \frac{c R_0 e^{-ct}}{s p}.$$

If $c$ is so small that $e^{-ct} \approx 1$ while $p$ rises from $p_0$ to $1$ (that is, $0 < c \ll s$), integrating from $p_0$ to $1$ gives

$$\frac{Q_\infty}{R_0} \approx \frac{c}{s} \log \frac{1}{p_0},$$

and with $p_0 = 1/N$ (one copy) the ratio is $(c/s)\log N$. Here $Q_\infty$ is the final population frequency of $A$, to be compared with its initial population frequency $(1 - p_0) R_0$, which is close to $R_0$ when $p_0$ is small. The approximation is accurate while $Q_\infty / R_0 \lesssim 0.1$ and overestimates the exact series near $Q_\infty/R_0 = 0.5$. A smaller frequency of $A$ need not mean a smaller heterozygosity $2x(1-x)$ at a given neutral locus (see the counterexample on the [exact recursion](maynard-smith-haigh-exact-hitchhiking-recursion.md) page), so no per-locus heterozygosity conclusion follows from the approximation alone.

## Expansion

Subtracting the $R$ equation from the $Q$ equation gives $\tfrac{d}{dt}(Q - R) = -c(Q - R)$. The solution of $\dot p = s p(1-p)$ from $p_0 \in (0,1)$ is the logistic trajectory, which stays in $(0, 1)$ and increases to $1$ for $s > 0$, so $p$ is a valid change of variable. Dividing the $Q$ equation by $\dot p = s p (1 - p)$ cancels the factor $1 - p$, leaving $dQ/dp = c R_0 e^{-ct}/(s p)$, and $\int_{p_0}^{1} dp/p = \log(1/p_0)$. The comparison with the exact recursion is the authors' Table 1 and Fig. 1 (numerical).

## Depends on

- [Maynard Smith–Haigh hitchhiking recursion and the final neutral frequency](maynard-smith-haigh-exact-hitchhiking-recursion.md)

## Proof depends on

- [Sweep trajectory solves the logistic equation](has-deriv-at-sweep-traj.md)
- [Sweep trajectory stays strictly between 0 and 1](sweep-traj-mem-ioo.md)

## Sources

- J. Maynard Smith and J. Haigh, "The hitch-hiking effect of a favourable gene", *Genetical Research* 23 (1974), 23–35, <https://doi.org/10.1017/S0016672300014634>. Section 2, equations (10)–(14), Table 1 and Fig. 1.
