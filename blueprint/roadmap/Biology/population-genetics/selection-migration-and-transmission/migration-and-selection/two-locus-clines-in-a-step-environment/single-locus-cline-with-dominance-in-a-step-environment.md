# Single-locus cline with dominance in a step environment

**Model.** A diallelic locus with allele frequency $P(x)$ on $\mathbb{R}$ is under diffusive migration and selection in a step environment

$$
\alpha(x)=\begin{cases}\alpha_+ & x\ge0,\\ -\alpha_- & x<0,\end{cases}\qquad \alpha_\pm>0,
$$

with constant dominance coefficient $h\in[-1,1]$ and selection intensity $\lambda>0$ (after rescaling by the migration variance). The cline is the solution of

$$
P''+\lambda\,\alpha(x)\,P(1-P)(1+h-2hP)=0,\qquad 0<P<1,\quad P(-\infty)=0,\ P(+\infty)=1,\quad P'(\pm\infty)=0 .
$$

Put $a_\pm=\sqrt{\lambda\alpha_\pm}$, $\phi(y,h)=3-2y+3h(1-y)^2$, $\xi_+=xa_+\sqrt{1-h}$ ($h<1$), $\xi_-=xa_-\sqrt{1+h}$ ($h>-1$), and let $a_0\in(0,1)$ be the unique solution of

$$
a_0^2\,\phi(a_0,h)=\frac{\alpha_+}{\alpha_++\alpha_-}.
$$

Let $F_+(y,h)=\bigl(2+(1-3h)y+\sqrt3\sqrt{1-h}\sqrt{\phi(1-y,-h)}\bigr)/(1-y)$ for $h<1$, $F_-(y,h)=1/F_+(1-y,-h)$ for $h>-1$, $A_\pm=F_\pm(a_0,h)$ and $Z_\pm(x)=A_\pm e^{\xi_\pm}$.

**Theorem.** There is a unique continuously differentiable solution $P$. For $x\ge0$ and $h<1$,

$$
P(x)=1-\frac{6(1-h)}{Z_++2(1-3h)+(1+3h)Z_+^{-1}},
$$

and for $x<0$ and $h>-1$,

$$
P(x)=\frac{6(1+h)}{(1-3h)Z_-+2(1+3h)+Z_-^{-1}};
$$

for $h=1$ one has $P(x)=1-12/(9+4(xa_++A_+)^2)$ on $x\ge0$, and for $h=-1$, $P(x)=12/(9+4(xa_--A_-)^2)$ on $x<0$, with the corresponding limiting constants $A_\pm$. Moreover $P(0)=a_0$, and the slope at the step,

$$
P'(0)=\sqrt{\frac{\lambda}{3}}\sqrt{\frac{\alpha_+\alpha_-}{\alpha_++\alpha_-}},
$$

is independent of the degree of dominance; for fixed $\alpha_++\alpha_-$ it is maximal when $\alpha_+=\alpha_-$ and tends to $0$ as $\alpha_+\to0$ or $\alpha_-\to0$.

## Depends on

- [Haldane's cline in a step environment](../../../haploid-selection-and-multiplicative-fitnesses/stationary-cline-in-a-step-environment.md)

## Expansion

Following Haldane, multiply the equation by $2P'$ and integrate on each half-line using $\partial_y(y^2\phi(y,h))=6y(1-y)(1+h-2hy)$: the boundary conditions give $(P')^2=\frac{\lambda\alpha_+}{3}(1-P^2\phi(P,h))$ on $x\ge0$ and $(P')^2=\frac{\lambda\alpha_-}{3}P^2\phi(P,h)$ on $x<0$. Continuity of $P'$ at $0$ forces the quartic equation for $a_0=P(0)$, and evaluating the left branch at $x=0$ gives $P'(0)$ in terms of the harmonic mean of $\alpha_+$ and $\alpha_-$, with $h$ cancelling. Integrating the resulting first-order equations $P'=\frac{a_+}{\sqrt3}(1-P)\sqrt{\phi(1-P,-h)}$ and $P'=\frac{a_-}{\sqrt3}P\sqrt{\phi(P,h)}$ with the initial value $a_0$ yields the explicit formulas; $h=0$ and $h=-1$ recover Haldane's classical cases.

## Sources

- Reinhard Bürger, "Two-locus clines on the real line with a step environment", *Theor. Popul. Biol.* 117 (2017), 1-22. <https://doi.org/10.1016/j.tpb.2017.08.002>
- Preprint version (the locators in this item follow its numbering): Reinhard Bürger, *Two-locus clines on the real line with a step environment*, arXiv (2017). Theorem 3.2 (explicit single-locus cline with dominance), Corollary 3.3 (properties; slope independent of dominance), Section 3. <https://doi.org/10.48550/arXiv.1708.03499>
