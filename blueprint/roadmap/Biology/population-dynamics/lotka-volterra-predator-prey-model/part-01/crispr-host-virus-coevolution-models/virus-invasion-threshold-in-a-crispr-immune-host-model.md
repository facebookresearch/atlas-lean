# Virus invasion threshold in a CRISPR immune-host model

**Model.** Let $x(t)$ and $y(t)$ be the densities of immune hosts (immunity level $p$) and sensitive hosts (innate immunity $s$, with $0\le s\le p\le 1$), and $z(t)$ the density of viruses. With immunity decay rate $l$, immunity acquisition rate $e$, virus death rate $d$, virus burst size $M$, encounter rate $b$, crowding coefficient $a\ge0$ and unit host growth rates,

$$\begin{aligned}
\dot x&=x\big(1-l-a(x+y)\big)-bxz(1-p)+esyz,\\
\dot y&=y+lx-ay(x+y)-byz(1-s)-esyz,\\
\dot z&=z\big(-d+bM\,(x(1-p)+y(1-s))-b\,(xp+ys)\big).
\end{aligned}$$

Here a virus that meets a host either reproduces (probability $1-p$ or $1-s$) or is destroyed. In the virus-dependent version the immunity of immune hosts is $p(z)=(1-s)e^{-kz}+s$ with $k>0$, declining from $1$ toward $s$ as the viral load grows.

**Statement 1 (trivial and virus-free equilibria).** The origin $O=(0,0,0)$ is an equilibrium for all parameters and is always unstable. If $a>0$, the virus-free equilibrium of sensitive hosts only, $A=(0,1/a,0)$, exists; it is asymptotically stable if

$$M<\frac{da+bs}{b(1-s)}$$

and unstable if the reverse strict inequality holds.

## Expansion

At $O$ the linearization has eigenvalue $1$ in the $y$ direction, so $O$ is unstable. At $A$ the Jacobian is triangular in the variables $(x,z)$ relative to $y$: the $x$ direction has eigenvalue $1-l-a\cdot\tfrac1a=-l<0$, the $y$ direction (logistic growth) has eigenvalue $-1$, and the $z$ direction has

$$\lambda_z=-d+\frac{b}{a}\big(M(1-s)-s\big),$$

the per-virus growth rate in a host population at carrying capacity $1/a$. Thus $\lambda_z<0$ exactly when $M(1-s)-s<da/b$, i.e. $M<(da+bs)/(b(1-s))$, which is the condition for viruses to fail to invade. Past this threshold the virus invades and, for constant $p$, a transcritical bifurcation exchanges stability between $A$ and an interior equilibrium; with the virus-dependent immunity $p(z)$ the paper finds Bogdanov-Takens points and long irregular, pseudo-chaotic oscillations of all three populations.

## Sources

- Berezovskaya FS, Wolf YI, Koonin EV, Karev GP, "Pseudo-chaotic oscillations in CRISPR-virus coevolution predicted by bifurcation analysis", Biol Direct 2014 Jul 2;9:13, Model (1), immunity function (3), Statement 1 and Propositions 2-4, <https://doi.org/10.1186/1745-6150-9-13>, PMCID PMC4096434.
