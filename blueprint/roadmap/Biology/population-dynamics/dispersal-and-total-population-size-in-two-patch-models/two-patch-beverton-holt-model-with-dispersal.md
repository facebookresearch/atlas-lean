# Two-patch Beverton–Holt model with symmetric dispersal

Let $r_A, r_B>1$ and $K_A, K_B>0$, and put $\xi_i=(r_i-1)/K_i$ for $i\in\{A,B\}$. The Beverton–Holt recruitment function of patch $i$ is

$$f_i(N)=\frac{r_iN}{1+\xi_iN},\qquad N\ge 0,$$

whose unique positive fixed point is the carrying capacity $K_i$. Growth precedes dispersal, and a fraction $\delta\in[0,1]$ of each patch moves to the other patch:

$$N_{A,t+1}=(1-\delta)f_A(N_{A,t})+\delta f_B(N_{B,t}),\qquad N_{B,t+1}=(1-\delta)f_B(N_{B,t})+\delta f_A(N_{A,t}).$$

Here $\delta=0$ means isolated patches, $\delta=1/2$ equalizes the two patches after one step (perfect mixing), and $\delta=1$ swaps the two populations every step.

**Global convergence (Lemma 1).** Assume $1<r_B\le r_A$. For each $\delta\in[0,1]$ the system has a unique fixed point $(N_A(\delta),N_B(\delta))$ in the open positive quadrant $(0,\infty)^2$, and

$$\lim_{t\to\infty}(N_{A,t},N_{B,t})=(N_A(\delta),N_B(\delta))$$

for every initial condition in $[0,\infty)^2\setminus\{(0,0)\}$ when $0<\delta<1$, and for every initial condition in $(0,\infty)^2$ when $\delta\in\{0,1\}$. The restriction at the endpoints is needed: from $(K_A,0)$ the orbit is fixed at $(K_A,0)$ when $\delta=0$ and alternates between $(K_A,0)$ and $(0,K_A)$ when $\delta=1$, so neither converges to the positive fixed point. (The source's Lemma 1 states the broad version; its recurrence gives these counterexamples.)

**Neutrality for equal capacities (Lemma 2).** If in addition $K_A=K_B$, then $N_A(\delta)+N_B(\delta)=K_A+K_B$ for every $\delta\in(0,1]$: dispersal does not change the asymptotic total population size.

## Depends on

This node has no prerequisites.

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

The map $(N_A,N_B)\mapsto((1-\delta)f_A(N_A)+\delta f_B(N_B),\,(1-\delta)f_B(N_B)+\delta f_A(N_A))$ is monotone (cooperative) and strictly subhomogeneous because each $f_i$ is increasing and concave with $f_i(0)=0$, $f_i'(0)=r_i>1$. Monotone-map theory then gives a unique positive fixed point. For $0<\delta<1$ the map sends every nonzero point of $[0,\infty)^2$ into the open quadrant after one step, so the fixed point attracts every nonzero orbit. At $\delta=0$ the coordinate axes are invariant, and at $\delta=1$ the map exchanges them, so attraction holds only for orbits starting with both patches positive; at $\delta=1$ it follows by applying the one-patch Beverton–Holt convergence to the two-step map $N_A\mapsto f_B(f_A(N_A))$. When $K_A=K_B=K$, the point $(K,K)$ is fixed for every $\delta$ because $f_A(K)=f_B(K)=K$, so uniqueness forces $N_A(\delta)+N_B(\delta)=2K$.

The well-defined total-size difference $H(\delta)=N_A(\delta)+N_B(\delta)-(K_A+K_B)$ is the object whose shape as a function of $\delta$ is classified in the companion article on the dispersal response of total size.

## Sources

- C. Grumbach, F. N. Reurik, J. Segura et al., *The effect of dispersal on asymptotic total population size in discrete- and continuous-time two-patch models*, Journal of Mathematical Biology (2023), <https://doi.org/10.1007/s00285-023-01984-8> (PMCID: PMC10514157). Equations (1)–(2), Section 3.1, Lemmas 1 and 2 (proofs in Appendix A.1).
