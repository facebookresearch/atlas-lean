# Control reproduction number under protective behaviour and alternative hosts

**Model.** A Ross–Macdonald-type vector–host model with $H$ humans, $M$ mosquitoes and $L$ alternative (non-human) hosts, $l = L/H$ and $\rho = M/H$. A fraction $p$ of humans adopts protective behaviour, which multiplies their exposure to bites by $q\in[0,1]$; mosquitoes keep a fixed biting rate, so bites are redistributed over available hosts with weight $c(p,q)+l$, where $c(p,q) = 1-p(1-q)$. Humans recover at rate $\gamma$, mosquitoes die at rate $\mu$, and $\beta_{H\leftarrow M}$, $\beta_{M\leftarrow H}$ are the transmission rates per bite. The basic reproduction number without protection is

$$R_0 = \frac{1}{1+l}\sqrt{\frac{\beta_{H\leftarrow M}\beta_{M\leftarrow H}}{\gamma\mu}\,\rho},$$

and the next-generation matrix of the linearisation at the disease-free equilibrium gives the control reproduction number

$$R_c(p,q) = R_0\,\frac{1+l}{c(p,q)+l}\,\sqrt{1-p(1-q^2)} .$$

**Theorem.** Let $p\in(0,1)$ and $q\in[0,1)$.

1. $R_c(p,q)<R_0$ if and only if $l > F(p,q) := \dfrac{(1-p)(1-q)}{\sqrt{1-p(1-q^2)}+q}$.
2. Without alternative hosts ($l=0$), protection never helps at the population level: $R_c(p,q)\ge R_0$, with equality at $p=1$, and the ratio $R_c/R_0$ decreases in $q$.
3. For $l>0$ and fixed $p$, $q\mapsto R_c(p,q)$ attains a minimum smaller than $R_0$ at $q = (1-p)/(1-p+l)$; and if $l\ge (1-q)/(1+q)$ then $R_c<R_0$ for every $p\in(0,1)$.

## Expansion

Because mosquitoes take a fixed number of blood meals, protecting some humans concentrates bites on the unprotected ones; transmission is a product of host-to-vector and vector-to-host terms, so the square root of the next-generation spectral radius combines the reduced exposure $\sqrt{1-p(1-q^2)}$ with the bite-concentration factor $(1+l)/(c(p,q)+l)$. Only diverting bites to alternative hosts ($l>0$) can make the first effect win, and comparing the two factors gives the threshold $F(p,q)$.

## Sources

- S. De Reggi, A. Pugliese, M. Sensi, C. Soresina, "A model for mosquito-borne epidemic outbreaks with information-dependent protective behaviour", *Journal of Mathematical Biology* 93(5) (2026), 58, Section 2, control reproduction number, Proposition 2, Corollaries 3–4 and Proposition 5, <https://doi.org/10.1007/s00285-026-02472-5> (preprint arXiv:2511.16802).
