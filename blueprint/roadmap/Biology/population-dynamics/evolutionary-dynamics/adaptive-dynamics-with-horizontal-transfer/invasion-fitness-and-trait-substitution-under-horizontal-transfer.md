# Invasion fitness and trait substitution under horizontal transfer

**Model.** Bacteria carry a trait $x$ inherited vertically (birth rate $b(x)$, death rate $d(x)$, logistic competition kernel $C(x,y)$, growth rate $r(x)=b(x)-d(x)$) and transferred horizontally: an $x$-individual meeting a $y$-individual converts it to $x$ at rate $\tau(x,y)/(\beta+\mu N)$, where $N$ is the population size; $(\beta,\mu)=(1,0)$ is density-dependent, $(0,1)$ frequency-dependent, and $\beta,\mu>0$ the Beddington–DeAngelis form. Let $\alpha(x,y)=\tau(x,y)-\tau(y,x)$ be the net transfer rate. With two traits $x,y$ and population scale $K\to\infty$, the rescaled densities converge to

$$\begin{aligned} \dot n^x&=\Big(r(x)-C(x,x)n^x-C(x,y)n^y+\frac{\alpha(x,y)}{\beta+\mu(n^x+n^y)}n^y\Big)n^x,\\ \dot n^y&=\Big(r(y)-C(y,x)n^x-C(y,y)n^y-\frac{\alpha(x,y)}{\beta+\mu(n^x+n^y)}n^x\Big)n^y . \end{aligned}$$

**Proposition (phase portrait).** If $C(x,x),C(y,y)>0$, then $1/(uv)$ is a Dulac function, so there are no periodic orbits in the open quadrant. The boundary equilibria are $(0,0)$ (unstable), $(\bar n^x,0)$ and $(0,\bar n^y)$ with $\bar n^x=r(x)/C(x,x)$; the transverse stability of $(\bar n^x,0)$ is given by the sign of the invasion fitness

$$S(y;x)=r(y)-\frac{C(y,x)\,r(x)}{C(x,x)}+\frac{\alpha(y,x)\,r(x)}{\beta C(x,x)+\mu r(x)} .$$

There are at most $3$ interior equilibria for Beddington–DeAngelis transfer, at most $2$ for frequency-dependent and at most $1$ for density-dependent transfer (or a line of equilibria), with the possible configurations fixed by an index argument.

**Invasion probability.** A single mutant $y$ in a resident population at $\bar n^x$ invades with probability, as $K\to\infty$,

$$[P(y;x)]_+,\qquad P(y;x)=\frac{S(y;x)}{b(y)+\tau(y,x)\bar n^x/(\beta+\mu\bar n^x)} .$$

**Theorem (trait substitution sequence).** Under rare mutations (mutation probability $p_K$ with $\log K\ll1/(Kp_K)\ll e^{VK}$ for every $V>0$) and the "invasion implies fixation" assumption, the population process at time scale $t/(Kp_K)$ converges to $\bar n^{Y_t}\delta_{Y_t}$, where $Y$ is a pure-jump process jumping from $x$ to $y$ at rate $b(x)\,\bar n^x\,[P(y;x)]_+\,m(x,dy)$, $m$ being the mutation kernel.

## Expansion

At a resident equilibrium, a rare mutant lineage is a birth–death process whose births include vertical reproduction $b(y)$ and conversions of residents $\tau(y,x)\bar n^x/(\beta+\mu\bar n^x)$, and whose deaths include natural death, competition and being converted back; its supercriticality and survival probability give $S$ and $P$. Because transfer adds the term $\alpha(y,x)r(x)/(\beta C(x,x)+\mu r(x))$ to invasion fitness, a trait that lowers growth ($r(y)<r(x)$) can still invade and fix if it transfers efficiently; iterating such substitutions along the trait substitution sequence can drive the population to ever lower size and even extinction (evolutionary suicide), with frequency-dependent transfer most prone to it.

## Sources

- Sylvain Billiard, Pierre Collet, Régis Ferrière, Sylvie Méléard, Viet Chi Tran, "Stochastic dynamics for adaptation and evolution of microorganisms", arXiv:1610.00983: Propositions 3.2 and 4.1 (large-population limits), Propositions 4.2–4.5 (Dulac function, boundary equilibria and invasion fitness, number and type of interior equilibria), Section 5.1 (invasion probability), Theorem 5.1 (trait substitution sequence). <https://doi.org/10.48550/arXiv.1610.00983> Published version: European Congress of Mathematics (2018) 525–550, <https://doi.org/10.4171/176-1/25>.
