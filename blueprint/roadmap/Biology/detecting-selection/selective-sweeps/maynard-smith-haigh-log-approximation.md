# Logarithmic approximation of hitchhiking at a tightly linked neutral locus

In the [haploid hitchhiking model](maynard-smith-haigh-exact-hitchhiking-recursion.md), replace the recursions by the differential equations

$$\dot p = s p (1 - p), \qquad \dot Q = c (1 - p)(R - Q), \qquad \dot R = c\, p\, (Q - R),$$

with $Q(0) = 0$, $R(0) = R_0$. Then $Q - R = -R_0 e^{-ct}$, and

$$\frac{dQ}{dp} = \frac{c R_0 e^{-ct}}{s p}.$$

If $c$ is so small that $e^{-ct} \approx 1$ while $p$ rises from $p_0$ to $1$ (that is, $0 < c \ll s$), integrating from $p_0$ to $1$ gives

$$\frac{Q_\infty}{R_0} \approx \frac{c}{s} \log \frac{1}{p_0},$$

and with $p_0 = 1/N$ (one copy) the reduction factor is $(c/s)\log N$. The approximation is accurate while $Q_\infty / R_0 \lesssim 0.1$ and overestimates the exact series near $Q_\infty/R_0 = 0.5$. The heterozygosity $H = 2R(1 - R)$ at the neutral locus is reduced correspondingly, most strongly at small $c/s$.

## Expansion

Subtracting the $R$ equation from the $Q$ equation gives $\tfrac{d}{dt}(Q - R) = -c(Q - R)$. Dividing the $Q$ equation by $\dot p = s p (1 - p)$ cancels the factor $1 - p$, leaving $dQ/dp = c R_0 e^{-ct}/(s p)$, and $\int_{p_0}^{1} dp/p = \log(1/p_0)$. The comparison with the exact recursion is the authors' Table 1 and Fig. 1 (numerical).

## Depends on

- [Maynard Smith–Haigh hitchhiking recursion and the final neutral frequency](maynard-smith-haigh-exact-hitchhiking-recursion.md)

## Sources

- J. Maynard Smith and J. Haigh, "The hitch-hiking effect of a favourable gene", *Genetical Research* 23 (1974), 23–35, <https://doi.org/10.1017/S0016672300014634>. Section 2, equations (10)–(14), Table 1 and Fig. 1.
