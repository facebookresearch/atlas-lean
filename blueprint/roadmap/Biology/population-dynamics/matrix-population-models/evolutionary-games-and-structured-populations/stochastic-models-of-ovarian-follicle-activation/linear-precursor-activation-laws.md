# Linear precursor-activation laws in follicle activation

**Model.** A follicle starts with $F_0=f_0$ precursor (flattened) cells and no proliferative (cuboidal) cells. The pure-jump Markov process $(F_t,C_t)$ on $\mathbb{N}^2$ has four events:

$$
\begin{aligned}
\mathcal{R}_1&:(F,C)\to(F-1,C+1)\ \text{at rate } \alpha_1F, &\quad \mathcal{R}_2&:(F,C)\to(F-1,C+1)\ \text{at rate } \beta\tfrac{FC}{F+C},\\
\mathcal{R}_3&:(F,C)\to(F,C+1)\ \text{at rate } \alpha_2F, &\quad \mathcal{R}_4&:(F,C)\to(F,C+1)\ \text{at rate } \gamma C,
\end{aligned}
$$

(spontaneous activation, auto-amplified activation, asymmetric precursor division, symmetric proliferative division), with $\alpha_1>0$ and $\alpha_2,\beta,\gamma\ge0$. Let $\tau=\inf\{t\ge0:F_t=0\}$ be the precursor extinction time and $C_\tau$ the number of proliferative cells at that time.

**Proposition (linear activation, $\beta=0$).** If $\beta=0$, then for every $t\ge0$ the precursor count $F_t$ is binomial with parameters $(f_0,e^{-\alpha_1t})$, and $\tau$ has the hypo-exponential (generalized Erlang) density

$$
f_\tau(t)=\alpha_1f_0e^{-\alpha_1t}\big(1-e^{-\alpha_1t}\big)^{f_0-1},\quad t\ge0,\qquad \mathbb{E}[\tau]=\frac{1}{\alpha_1}\sum_{k=1}^{f_0}\frac1k.
$$

**Proposition (first moment of $C_\tau$, $\beta=0$).** $\mathbb{E}[C_\tau]<\infty$ iff $\alpha_1>\gamma$. Moreover:

- without symmetric division ($\gamma=0$): $\mathbb{E}[C_\tau]=f_0\big(1+\alpha_2/\alpha_1\big)$;
- without asymmetric division ($\alpha_2=0$): $\mathbb{E}[C_\tau]=1+\sum_{k=1}^{f_0-1}\frac{(f_0-k)!}{\big((f_0-k)-\gamma/\alpha_1\big)!}$, where $(m-x)!:=\prod_{i=1}^m(i-x)$ for $m\in\mathbb{N}^*$, $x\in[0,1)$.

## Expansion

With $\beta=0$ each precursor activates independently after an $\mathrm{Exp}(\alpha_1)$ time, so $F_t$ counts survivors of $f_0$ independent exponentials and $\tau$ is their maximum; the density and the harmonic-sum mean follow. For $\gamma=0$ each precursor contributes itself plus a Poisson number of asymmetric daughters with mean $\alpha_2/\alpha_1$ during its lifetime. For $\alpha_2=0$ the proliferative population is a Yule process fed by activations; conditioning on the successive activation epochs and using $\mathbb{E}[e^{\gamma E}]$ for exponential gaps gives the product formula, which diverges exactly when $\gamma\ge\alpha_1$.

## Depends on

- [Gillespie direct method (stochastic simulation algorithm)](../../../../systems-biology/part-01/gillespie-direct-method.md)

## Sources

- Frédérique Clément, Frédérique Robin, Romain Yvinec, "Stochastic nonlinear model for somatic cell population dynamics during ovarian follicle activation", arXiv:1903.01316: Section "Model design and formulation" (events R1–R4); Section "Model analysis", propositions on the laws of the linear extinction time and on the first moment of the proliferative count. <https://doi.org/10.48550/arXiv.1903.01316>
