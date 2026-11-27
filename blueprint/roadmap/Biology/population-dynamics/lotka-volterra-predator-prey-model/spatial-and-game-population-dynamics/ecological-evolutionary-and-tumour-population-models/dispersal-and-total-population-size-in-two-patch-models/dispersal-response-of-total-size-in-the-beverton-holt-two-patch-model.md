# Response of total population size to dispersal in the two-patch Beverton–Holt model

In the [two-patch Beverton–Holt model](two-patch-beverton-holt-model-with-dispersal.md) with $1<r_B\le r_A$ and $K_A\ne K_B$, let

$$H(\delta)=N_A(\delta)+N_B(\delta)-(K_A+K_B),\qquad \delta\in[0,1],$$

be the gain in asymptotic total population size caused by dispersal at rate $\delta$. Then:

1. **Initial slope (Lemma 4).**

$$H'(0^+)=\frac{(r_A-r_B)(K_A-K_B)}{(r_A-1)(r_B-1)}.$$

So weak dispersal is beneficial exactly when the patch with the larger growth rate also has the larger carrying capacity.
2. **At most one sign change (Lemma 3).** Define

$$\tilde\delta=\frac{K_AK_B(r_A-1)(r_B-1)(r_A-r_B)}{\bigl(K_A(r_B-1)+K_B(r_A-1)\bigr)\bigl(K_Ar_A(r_B-1)-K_Br_B(r_A-1)\bigr)}.$$

If $r_A=r_B$, or $K_Ar_A(r_B-1)=K_Br_B(r_A-1)$, or $\tilde\delta\notin(0,1]$, then $\delta=0$ is the only zero of $H$; otherwise the zeros of $H$ on $[0,1]$ are exactly $0$ and $\tilde\delta$.
3. **Four response scenarios (Theorem 1).** Assume $1<r_B<r_A$ and set $c=\sqrt{r_A}(r_B-1)/\bigl(\sqrt{r_B}(r_A-1)\bigr)$, so $0<c<1$. With $\delta_{\max}$ the explicit maximizer location defined in the source:
   - if $c\le K_B/K_A<1$ and $\delta_{\max}\notin(0,1)$, $H$ is positive on $(0,1]$ and strictly increasing on $[0,1]$ (monotonically beneficial); this case forces $K_B/K_A>c$;
   - if $c\le K_B/K_A<1$ and $\delta_{\max}\in(0,1)$, $H$ is positive on $(0,1)$, strictly increasing on $[0,\delta_{\max})$ and strictly decreasing on $(\delta_{\max},1]$ (unimodally beneficial). At the endpoint, $H(1)>0$ if $K_B/K_A>c$ and $H(1)=0$ if $K_B/K_A=c$: for example $(r_A,r_B,K_A,K_B)=(8,2,7,2)$ has $K_B/K_A=c=2/7$ and, by the closed forms below, $(N_A(1),N_B(1))=(3,6)$, so $H(1)=0$;
   - if $K_B/K_A<c$, then $0<\delta_{\max}<\tilde\delta<1$ and $H$ is positive and increasing on $(0,\delta_{\max})$, positive and decreasing on $(\delta_{\max},\tilde\delta)$, and negative and decreasing on $(\tilde\delta,1]$ (beneficial turning detrimental);
   - if $K_B/K_A>1$, $H$ is negative and strictly decreasing on $(0,1]$ (monotonically detrimental).

If $r_A=r_B$, $H$ is negative and strictly decreasing on $(0,1]$ for every $K_A\ne K_B$ (Remark 1). The fixed point at $\delta=1$ is (Corollary 1)

$$N_A(1)=\frac{K_AK_B(r_Ar_B-1)}{K_Ar_A(r_B-1)+K_B(r_A-1)},\qquad N_B(1)=\frac{K_AK_B(r_Ar_B-1)}{K_A(r_B-1)+K_Br_B(r_A-1)},$$

and in the monotonically beneficial scenario the maximal total population size is attained there.

## Depends on

- [Two-patch Beverton–Holt model with symmetric dispersal](two-patch-beverton-holt-model-with-dispersal.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

At $\delta=0$ the fixed point is $(K_A,K_B)$ and $f_i'(K_i)=1/r_i$ because $1+\xi_iK_i=r_i$. Differentiating the fixed-point equation $N_A=(1-\delta)f_A(N_A)+\delta f_B(N_B)$ at $\delta=0$ gives $N_A'(0)(1-1/r_A)=K_B-K_A$, so $N_A'(0)=r_A(K_B-K_A)/(r_A-1)$, and symmetrically $N_B'(0)=r_B(K_A-K_B)/(r_B-1)$. Their sum is the stated $H'(0^+)$. At $\delta=1$ the fixed point solves $N_A=f_B(N_B)$, $N_B=f_A(N_A)$, which is linear after inversion and gives the closed forms. Eliminating $\delta$ from the fixed-point equations under the constraint $N_A+N_B=K_A+K_B$ yields a linear equation in $\delta$ whose nonzero root is $\tilde\delta$.

A numerical check with the source's scenario (c) parameters $r_A=3.4$, $r_B=1.5$, $K_A=8.4$, $K_B=1.37$ gives $\tilde\delta\approx0.375$ with $H$ changing sign there, and $H'(0^+)\approx11.13$, matching the formula.

## Sources

- C. Grumbach, F. N. Reurik, J. Segura et al., *The effect of dispersal on asymptotic total population size in discrete- and continuous-time two-patch models*, Journal of Mathematical Biology (2023), <https://doi.org/10.1007/s00285-023-01984-8> (PMCID: PMC10514157). Equations (5)–(8), Lemmas 3–4, Proposition 1, Theorem 1, Remark 1 and Corollary 1 (Section 3.1).
