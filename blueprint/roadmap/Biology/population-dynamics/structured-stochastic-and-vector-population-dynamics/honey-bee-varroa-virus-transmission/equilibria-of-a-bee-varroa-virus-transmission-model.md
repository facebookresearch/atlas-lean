# Equilibria of a bee–Varroa virus transmission model

**Model.** In a honey bee colony infested by *Varroa destructor*, let $B,I$ be healthy and virus-infected adult bees and $M,N$ healthy and virus-carrying mites. Bees are born at constant daily rate $b$, healthy or infected in proportion to the fractions of healthy and infected bees (vertical transmission through nurse bees); infected mites infect healthy bees at rate $\lambda$, bee-to-bee transmission occurs at rate $\gamma$, bee mortality is $m$ with extra virus mortality $\mu$. Healthy mites grow logistically (rate $r$, capacity $K$), acquire the virus from infected bees ($\beta$) or infected mites ($\delta$), and all mites suffer bee-grooming mortality $e$ per bee; infected mites die at rate $n$ with crowding $p$:

$$B'=b\frac{B}{B+I}-\lambda BN-\gamma BI-mB,\qquad I'=b\frac{I}{B+I}+\lambda BN+\gamma BI-(m+\mu)I,$$

$$M'=r\Bigl(1-\frac{M+N}{K}\Bigr)(M+N)-\beta MI-\delta MN-eMB,\qquad N'=-nN-pN(N+M)+\beta MI+\delta MN-eNB .$$

**Theorem (well-posedness).** For initial data in the biological domain there is a unique global solution that stays in it, and

$$\frac{b}{m+\mu}\le\liminf_{t\to\infty}(B+I)\le\limsup_{t\to\infty}(B+I)\le\frac bm,\qquad M(t)+N(t)\le\max\{M(0)+N(0),K\}.$$

**Equilibria.** On the boundary:

- $E_1=(b/m,0,0,0)$ (healthy colony, no mites), always feasible, with eigenvalues $-m$, $(b\gamma-m\mu)/m$, $(mr-be)/m$, $-(be+mn)/m$; it is stable iff $b\gamma<m\mu$ and $mr<be$ (grooming outpaces mite growth);
- $E_2=(0,b/(m+\mu),0,0)$ (fully infected colony, no mites), always feasible, stable iff $b\gamma-m\mu-\mu^2>0$, $n>r$ and $b\beta>(m+\mu)\,rn/(n-r)$;
- $E_3=\bigl(b/m,0,\tfrac Kr(r-\tfrac{eb}m),0\bigr)$ (healthy bees with virus-free mites), feasible iff $r\ge eb/m$;
- $E_4=\bigl(\tfrac{\mu^2-b\gamma+m\mu}{\mu\gamma},\ \tfrac{b\gamma-m\mu}{\mu\gamma},\ 0,0\bigr)$ (endemic virus without mites), feasible iff $0<b\gamma-m\mu<\mu^2$, with total colony size $B+I=\mu/\gamma$;
- an equilibrium with mites and no healthy bees, found as the intersection of two conics, and an interior coexistence equilibrium studied numerically.

Bee-to-bee transmission alone can make the virus endemic ($b\gamma>m\mu$) even without mites, and mites can be excluded entirely when grooming removal at the mite-free colony size, $eb/m$, exceeds their growth rate $r$.

## Expansion

Positivity and boundedness follow because adding the bee equations gives $(B+I)'=b-m(B+I)-\mu I$, squeezed between $b-(m+\mu)(B+I)$ and $b-m(B+I)$, while adding the mite equations gives logistic growth minus nonnegative losses. Equilibria are classified by which populations vanish; at each boundary point the Jacobian is block triangular, so its spectrum splits into explicit eigenvalues plus at most a $2\times2$ block handled by the Routh–Hurwitz trace and determinant conditions, as for $E_2$ where $\operatorname{tr}<0$ and $\det>0$ reduce to the stated inequalities.

## Sources

- Sara Bernardi, Ezio Venturino, "Viral epidemiology of the adult Apis Mellifera infested by the Varroa destructor mite", Heliyon 2 (2016), e00101, <https://doi.org/10.1016/j.heliyon.2016.e00101>. Published version of arXiv:1510.05167, cited next; locators there refer to the arXiv version.
- S. Bernardi, E. Venturino, "Viral epidemiology of the adult Apis Mellifera infested by the Varroa destructor mite", arXiv:1510.05167 (2015), Section 2 (model and simplifying assumptions), Theorem 3.1, the equilibria section (feasibility of $E_1$–$E_5$) and the local stability analysis of $E_1$ and $E_2$. <https://doi.org/10.48550/arXiv.1510.05167>
