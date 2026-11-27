# Moment criterion for proliferative cells at precursor extinction

**Model.** A follicle starts with $F_0=f_0$ precursor (flattened) cells and no proliferative (cuboidal) cells. The pure-jump Markov process $(F_t,C_t)$ on $\mathbb{N}^2$ has four events:

$$
\begin{aligned}
\mathcal{R}_1&:(F,C)\to(F-1,C+1)\ \text{at rate } \alpha_1F, &\quad \mathcal{R}_2&:(F,C)\to(F-1,C+1)\ \text{at rate } \beta\tfrac{FC}{F+C},\\
\mathcal{R}_3&:(F,C)\to(F,C+1)\ \text{at rate } \alpha_2F, &\quad \mathcal{R}_4&:(F,C)\to(F,C+1)\ \text{at rate } \gamma C,
\end{aligned}
$$

(spontaneous activation, auto-amplified activation, asymmetric precursor division, symmetric proliferative division), with $\alpha_1>0$ and $\alpha_2,\beta,\gamma\ge0$. Let $\tau=\inf\{t\ge0:F_t=0\}$ be the precursor extinction time and $C_\tau$ the number of proliferative cells at that time.

**Theorem.** Assume $\alpha_1>0$. For every $p\ge1$,

$$
\mathbb{E}\big[C_\tau^{\,p}\big]<\infty\iff p\,\gamma<\alpha_1+\beta.
$$

In particular $\mathbb{E}[C_\tau]<\infty$ iff the maximal activation rate exceeds the proliferation rate, $\alpha_1+\beta>\gamma$. The asymmetric-division rate $\alpha_2$ plays no role in the criterion.

**Auxiliary result.** For independent processes $\tilde F$ (pure death at rate $\tilde\alpha f$) and $\tilde C$ (immigration–birth at rate $\tilde\beta+\tilde\gamma c$, $\tilde C(0)=n\ge1$) with $\tilde\tau$ the extinction time of $\tilde F$ from $f_0$, $\mathbb{E}[\tilde C_{\tilde\tau}^{\,p}]<\infty$ iff $p\tilde\gamma<\tilde\alpha$, and for $\tilde\gamma>0$,

$$
\mathbb{E}\big[\tilde C_{\tilde\tau}\big]=n\,\frac{f_0!}{(f_0-\tilde\gamma/\tilde\alpha)!}+\frac{\tilde\beta}{\tilde\gamma}\Big(\frac{f_0!}{(f_0-\tilde\gamma/\tilde\alpha)!}-1\Big).
$$

## Expansion

The last precursor dies at rate between $\alpha_1$ (no feedback) and $\alpha_1+\beta$ (since $\beta\frac{FC}{F+C}\le\beta F$ and $\frac{C}{1+C}\to1$ when $F=1$ and $C$ is large). Meanwhile $C$ grows like a Yule process at rate $\gamma$, so $C_\tau$ has a power-law tail $\mathbb{P}(C_\tau>x)\approx x^{-(\alpha_1+\beta)/\gamma}$, whose $p$-th moment is finite iff $p\gamma<\alpha_1+\beta$. The proof makes this precise by coupling $(F,C)$, stopped when $C$ first reaches $n$, between the independent auxiliary processes above with death rates $\alpha_1$ and $\alpha_1+\beta\frac{n}{1+n}$, then letting $n\to\infty$. Biologically, a finite mean number of proliferative cells at the end of activation requires activation to outpace proliferation.

## Depends on

- [Linear precursor-activation laws in follicle activation](linear-precursor-activation-laws.md)

## Sources

- Frédérique Clément, Frédérique Robin, Romain Yvinec, "Stochastic nonlinear model for somatic cell population dynamics during ovarian follicle activation", arXiv:1903.01316: Section "Model analysis": Theorem 1 (moment criterion), Hypotheses 1 and 3, coupling definitions; Appendix proposition on the auxiliary death and immigration-birth processes. <https://doi.org/10.48550/arXiv.1903.01316>
