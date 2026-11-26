# Dynamically consistent Euler discretization of ethanol metabolism

**Scheme.** For the gut–blood–liver ethanol model $A'=-aA$, $B'=bC-bB+aA$, $C'=bB-bC-f(C)$ with a rate function $f$ satisfying (P) ($f$ continuous, nonnegative, vanishing only at $0$), consider the explicit Euler scheme with step $\Delta t>0$:

$$A_{n+1}=A_n-a\Delta t\,A_n,\qquad B_{n+1}=B_n+b\Delta t\,(C_n-B_n)+a\Delta t\,A_n,\qquad C_{n+1}=C_n+b\Delta t\,(B_n-C_n)-\Delta t\,f(C_n).$$

Assume in addition **(P\*)**: $f'(0)$ exists. Then $g(C)=f(C)/C$ for $C\ne0$, $g(0)=f'(0)$, is continuous and $f(C)=Cg(C)$. For nonnegative initial data put $S_0=A_0+B_0+C_0$ and $M=\max_{0\le C\le S_0}g(C)$.

**Lemma (positivity).** If

$$\Delta t\le\min\Big\{\frac1a,\ \frac1{b+M}\Big\},$$

then $A_n,B_n,C_n\ge0$ for all $n$, and both $A_n$ and $A_n+B_n+C_n$ are nonincreasing.

**Theorem (local stability).** Under this step-size condition the unique equilibrium $(0,0,0)$ of the scheme is locally asymptotically stable for all parameter values.

**Theorem (global stability).** Under the same step-size condition the equilibrium $(0,0,0)$ is globally asymptotically stable for all parameter values: every nonnegative orbit converges to $0$. (An earlier theorem in the same paper proves this under the extra assumption $\min_{0\le C\le S_0}g(C)>0$; the general statement drops it.)

So under one explicit step-size restriction the discrete model reproduces the qualitative dynamics of the continuous model (positivity, monotone clearance, a unique globally attracting ethanol-free state). Under the extra assumption $\min_{[0,S_0]}g=m>0$ one has $mC\le f(C)\le MC$ on $[0,S_0]$, the linear-sandwich property common in biological rate laws.

## Expansion

*Positivity.* Rewrite the scheme as $A_{n+1}=(1-a\Delta t)A_n$, $B_{n+1}=(1-b\Delta t)B_n+b\Delta t\,C_n+a\Delta t\,A_n$, $C_{n+1}=(1-b\Delta t-g(C_n)\Delta t)C_n+b\Delta t\,B_n$. The step-size condition makes every coefficient nonnegative because $g(C_n)\le M$ while the total stays below $S_0$. The total changes by $-\Delta t\,f(C_n)\le0$.

*Local stability.* The Jacobian at $0$ is block lower triangular, with eigenvalue $1-a\Delta t$ and a $2\times2$ block $J_1$ for $(B,C)$ satisfying $|\mathrm{tr}\,J_1|<1+\det J_1<2$ (Jury conditions), so all eigenvalues lie in the open unit disk.

*Global stability.* With $V_n=(A_n+B_n+C_n)^2$,

$$V_{n+1}-V_n=-\Delta t\,f(C_n)\big[(A_{n+1}+B_{n+1}+C_{n+1})+(A_n+B_n+C_n)\big]\le0 ,$$

and $\Delta V=0$ only when $C_n=0$. LaSalle's invariance principle for maps then gives convergence to $0$. Under the extra lower bound $m>0$, an alternative proof compares the orbit with a positive linear system $x_{n+1}\le Px_n$ whose matrix $P$ has spectral radius below one.

## Depends on

- [Global stability of the generalized ethanol metabolism model](global-stability-of-the-generalized-ethanol-metabolism-model.md)

## Sources

- Manh Tuan Hoang, Thi Kim Quy Ngo, Benjamin Wacker, "On a Generalized Compartment Model for Ethanol Metabolism in the Human Body", arXiv:2606.30439 (2026): discrete model in Section 1, Lemma 3.1 (positivity under the step-size condition), Theorem 3.2 (local stability), Theorem 3.3 (global stability with a positive lower bound on $g$), Remark 3.4, Theorem 3.5 (global stability without that bound). <https://doi.org/10.48550/arXiv.2606.30439>
