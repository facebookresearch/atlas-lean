# Response of total population size to dispersal in the two-patch logistic model

Let $r_A,r_B>0$, $0<K_A<K_B$ and $\delta\ge0$. The continuous-time two-patch logistic model with symmetric dispersal is

$$\frac{dN_A}{dt}=r_AN_A\Bigl(1-\frac{N_A}{K_A}\Bigr)-\delta(N_A-N_B),\qquad \frac{dN_B}{dt}=r_BN_B\Bigl(1-\frac{N_B}{K_B}\Bigr)-\delta(N_B-N_A).$$

For each $\delta\ge0$ it has a unique positive equilibrium $(N_A(\delta),N_B(\delta))$, with $K_A<N_A(\delta)<N_B(\delta)<K_B$ for $\delta>0$. For $\delta>0$ it attracts every solution with nonnegative, not identically zero initial data; at $\delta=0$ the patches decouple, both axes are invariant, and the equilibrium $(K_A,K_B)$ attracts exactly the solutions with both initial densities positive. Let $H(\delta)=N_A(\delta)+N_B(\delta)-(K_A+K_B)$. Then

$$H(0)=0,\qquad H(\infty):=\lim_{\delta\to\infty}H(\delta)=\frac{(K_B-K_A)(r_BK_A-r_AK_B)}{r_BK_A+r_AK_B},\qquad H'(0^+)=\frac{(K_B-K_A)(r_B-r_A)}{r_Ar_B}.$$

Put $\kappa=(r_A+3r_B)/(r_B+3r_A)$. The response falls into four scenarios (Theorem 2):

1. if $r_A<r_B$ and $r_B/K_B\ge\kappa\,r_A/K_A$: $H>0$ and $H'>0$ on $(0,\infty)$ (monotonically beneficial);
2. if $r_A<r_B$ and $r_A/K_A\le r_B/K_B<\kappa\,r_A/K_A$: $H>0$ on $(0,\infty)$ and there is $\delta_{\max}>0$ with $H$ increasing before and decreasing after it (unimodally beneficial);
3. if $r_A<r_B$ and $r_B/K_B<r_A/K_A$: $H$ rises then falls, $H(\infty)<0$, and there is a unique $\tilde\delta>0$ with $H>0$ on $(0,\tilde\delta)$ and $H<0$ on $(\tilde\delta,\infty)$ (beneficial turning detrimental);
4. if $r_A>r_B$: $H<0$ and $H'<0$ on $(0,\infty)$ (monotonically detrimental).

If $r_A=r_B$, $H$ is negative and strictly decreasing on $(0,\infty)$ with $H'(0^+)=0$.

## Depends on

This node has no prerequisites.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

At $\delta=0$ the equilibrium is $(K_A,K_B)$ and the logistic slopes there are $-r_A$ and $-r_B$. Implicit differentiation gives $N_A'(0)=(K_B-K_A)/r_A$ and $N_B'(0)=(K_A-K_B)/r_B$, whose sum is $H'(0^+)$. As $\delta\to\infty$ the patches equalize at the common value $N$ solving $r_AN(1-N/K_A)+r_BN(1-N/K_B)=0$, that is $N=(r_A+r_B)K_AK_B/(r_AK_B+r_BK_A)$, and $2N-K_A-K_B$ simplifies to $H(\infty)$. The scenario boundaries come from the signs of $H'(0^+)$, $H(\infty)$ and the large-$\delta$ derivative criterion. The four scenarios mirror the discrete-time ones; the discrete-time threshold $\kappa=(r_B+r_Ar_B-2)/(r_A+r_Ar_B-2)$ for $\delta\in[0,1/2]$ plays the role of $\kappa$ (Proposition 2). The discrete-time counterpart is the [two-patch Beverton–Holt response](dispersal-response-of-total-size-in-the-beverton-holt-two-patch-model.md), which is not used here.

## Sources

- C. Grumbach, F. N. Reurik, J. Segura et al., *The effect of dispersal on asymptotic total population size in discrete- and continuous-time two-patch models*, Journal of Mathematical Biology (2023), <https://doi.org/10.1007/s00285-023-01984-8> (PMCID: PMC10514157). Equations (3)–(4) and (12), Section 4.1 (Theorem 2, Remark 2), Section 4.2 (Proposition 2), and Appendix C; the formulas for $H(\infty)$ and $H'(0^+)$ are quoted there from Gao and Lou (2022) and the existence and ordering of equilibria from Arditi et al. (2015).
