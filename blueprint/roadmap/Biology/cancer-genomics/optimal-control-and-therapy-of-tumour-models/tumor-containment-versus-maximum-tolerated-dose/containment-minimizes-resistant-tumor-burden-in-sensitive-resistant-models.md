# Containment minimizes resistant tumor burden in sensitive–resistant models

**Model.** A tumor consists of treatment-sensitive cells $S$ and fully resistant cells $R$, with total size $N=S+R$, under a treatment level $L(t)\in[0,L_{\max}]$ (piecewise $C^1$):

$$\frac{dN}{dt}=f_N(N,R,L),\qquad \frac{dR}{dt}=f_R(N,R),$$

where, on $R_0\le R\le N\le N_{\rm crit}$, $f_N$ is non-increasing in $L$ and positive when $L=0$ (untreated tumors grow), and $f_R$ is positive and non-increasing in $N$ (resistant cells always grow, but more slowly in larger tumors: competition). No monotonicity of the sensitive growth rate in $R$ is assumed, so Norton–Simon chemotherapy models and mutations from sensitive to resistant cells are included. Treatment fails when $N$ exceeds a tolerable size $N_{\rm tol}\ge N_0$; the patient dies at $N_{\rm crit}\ge N_{\rm tol}$.

Treatments: *MTD* ($L\equiv L_{\max}$); *containment at $N_{\rm tol}$* (no treatment until $N=N_{\rm tol}$, then the dose that keeps $dN/dt=0$ while possible, then $L_{\max}$); *intermittent containment* (keep $N$ between $N_{\min}$ and $N_{\rm tol}$); an arbitrary *alternative* treatment with $L=L_{\max}$ whenever $N>N_{\rm tol}$; and the idealized versions (ideal MTD removes all sensitive cells at once; ideal containment holds $N=N_{\rm tol}$ while sensitive cells remain).

**Proposition (dose ordering).** If $L_1(t)\le\bar L\le L_2(t)$ for all $t$, then $R_1(t)\le R_2(t)$ for all $t$; in particular a higher constant dose, or treating earlier, never reduces the resistant population.

**Proposition (containment minimizes resistance).** For all $t\ge0$,

$$R_{\rm noTreat}(t)\le R_{\rm Cont}(t)\le R_{\rm alt}(t)\le R_{\rm MTD}(t).$$

**Proposition (ideal containment is optimal).** $t_{\rm alt}\le t_{\rm idCont}$ for every alternative treatment. If the alternative treatment eliminates the sensitive cells before failing, then $t_{\rm alt}\ge t_{\rm idMTD}$, $R_{\rm idCont}\le R_{\rm alt}\le R_{\rm idMTD}$ at all times and $N_{\rm idCont}\le N_{\rm alt}\le N_{\rm idMTD}$ after $t_{\rm alt}$: ideal containment maximizes and ideal MTD minimizes time to treatment failure and survival time.

**Proposition (reference ordering).** $t_{\rm idMTD}\le t_{\rm del\text{-}idMTD}\le t_{\rm idInt}\le t_{\rm idCont}$, and $R_{\rm noTreat}\le R_{\rm Cont}\le R_{\rm Int}\le R_{\rm del\text{-}MTD}\le R_{\rm MTD}\le R_{\rm idMTD}$ pointwise in time.

## Expansion

Because $\dot R=f_R(N,R)>0$, the resistant count is strictly increasing and can serve as a clock. Writing $\tilde N(r)$ and $\tilde S(r)$ for tumor sizes at the moment $R=r$, a treatment with pointwise larger $\tilde N(r)$ makes resistant cells grow more slowly (competition), so it reaches every resistant level later: comparison along $r$ replaces comparison along $t$. A lower dose keeps more sensitive cells, hence a larger tumor at each resistant level, hence slower resistance; this comparison principle on the resistant-size axis is what removes the earlier assumption that sensitive growth be non-increasing in $R$. Containment keeps the tumor as large as tolerable for as long as possible, maximizing competitive suppression of resistant cells.

## Sources

- Frank Alvarez, Yannick Viossat, "Tumor containment for Norton-Simon models", arXiv:2211.17041: Section 2 (model and treatments), Propositions 1–2 (dose ordering), Propositions 3–4 (containment minimizes resistance), Proposition 5 (ideal containment and ideal MTD), Propositions 6–7 (intermittent and reference treatments), Lemmas 9–11 (comparison along resistant population size). <https://doi.org/10.48550/arXiv.2211.17041> Published version: Journal of Mathematical Biology 88 (2024) 41, <https://doi.org/10.1007/s00285-024-02062-3>.
