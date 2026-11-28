# Slow–fast structure of the pairwise SIRS model

**Setting.** In the [pairwise SIRS equations](pairwise-sirs-equations-and-the-edge-reproduction-number.md) on a degree-$n$ network ($n > 2$), let the waning rate $\epsilon$ be small compared with $\beta, \gamma$, and assume $\mathcal{R}_0 = \beta(n-2)/\gamma > 1$.

**Fast limit** ($\epsilon = 0$). Along every orbit $[S]$ and $[SS]$ decrease, $[I], [SI], [II] \to 0$, and

$$V = \ln[SS] - \frac{2(n-1)}{n}\ln[S]$$

is a constant of motion, so $[SS]\,(t) = [SS]_0\big([S]\,(t)/[S]_0\big)^{2(n-1)/n}$ for all $t$.

**Critical manifold.** The disease-free states $C_0 = \{[I] = [SI] = [II] = 0\}$ form a manifold of equilibria of the fast system. The linearization on $C_0$ has eigenvalues $0, 0$ (slow variables $[S], [SS]$), $-\gamma, -2\gamma$, and

$$\lambda_5 = \beta(n-1)\frac{[SS]}{n[S]} - (\gamma + \beta),$$

so $C_0$ is attracting below and repelling above the line of lost hyperbolicity

$$[SS] = L[S], \qquad L = \frac{n(\beta + \gamma)}{\beta(n-1)} .$$

An initial condition in the repelling region produces an outbreak that ends at a point of the attracting region, determined explicitly by the constant of motion.

**Slow manifold and slow flow.** For $\epsilon > 0$, $C_0$ remains invariant and is, by Fenichel theory, a slow manifold (all slow manifolds are exponentially close to it where it is normally hyperbolic). On it, in slow time $\tau = \epsilon t$,

$$\dot{[S]} = 1 - [S], \qquad \dot{[SS]} = 2(n[S] - [SS]),$$

so $[S] \to 1$, $[SS] \to n$, and the parabola $\Gamma = \{[SS] = n[S]^2\}$ attracts uniformly: the distance $|[SS] - n[S]^2|$ decays as $e^{-2\tau}$. The endemic equilibrium lies $O(\epsilon)$ close to the line $[SS] = L[S]$.

## Depends on

- [Pairwise SIRS equations and the edge reproduction number](pairwise-sirs-equations-and-the-edge-reproduction-number.md)

## Expansion

Differentiating $V$ along the fast flow, $[SS]'/[SS] = -2\beta\frac{n-1}{n}\frac{[SI]}{[S]}$ and $[S]'/[S] = -\beta\frac{[SI]}{[S]}$, so $\frac{d}{dt}V = 0$. The fifth eigenvalue is the growth rate of $[SI]$ at a disease-free state: a single infected edge spreads iff $\beta\frac{n-1}{n}\frac{[SS]}{[S]} > \beta + \gamma$, which at the fully susceptible state $[SS] = n[S] = n$ is $\beta(n-1) > \beta + \gamma$, i.e. $\mathcal{R}_0 > 1$. The global picture is a relaxation-type cycle: slow drift along $C_0$ toward $([S],[SS]) = (1, n)$ through the attracting region, crossing of the line $[SS] = L[S]$ (where normal hyperbolicity fails and canard-like delayed loss of stability can occur), a fast outbreak back into the attracting region, and repetition with decreasing amplitude toward the endemic equilibrium. The slow flow's attraction to $\Gamma$, the locus where edges are uncorrelated ($[SS] = n[S]^2$), shows that slow replenishment of susceptibles erases pair correlations built up during outbreaks.

## Sources

- H. Jardón-Kojakhmetov, C. Kuehn, A. Pugliese, M. Sensi, "A geometric analysis of the SIRS epidemiological model on a homogeneous network", Journal of Mathematical Biology (2021), fast limit (14), Proposition 2, Remark 3 with equation (24), critical manifold (25)–(27), Propositions 3–5, slow flow (32)–(33) and Lemma 3, <https://doi.org/10.1007/s00285-021-01664-5>.
