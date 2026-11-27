# Poisson-gamma transition law of the Feller diffusion

The Feller diffusion with parameter $\alpha\in\mathbb R$ has generator

$$\mathcal L=\tfrac12x\frac{\partial^2}{\partial x^2}+\alpha x\frac{\partial}{\partial x},$$

equivalently $dX=\sqrt{X}\,dW+\alpha X\,dt$; it is subcritical, critical or supercritical as $\alpha<0$, $=0$ or $>0$. Set

$$\mu(t;\alpha)=\frac{2\alpha e^{\alpha t}}{e^{\alpha t}-1},\qquad\beta(t;\alpha)=\frac{e^{\alpha t}-1}{2\alpha}\quad(\alpha\ne0),\qquad\mu(t;0)=\frac2t,\ \beta(t;0)=\frac t2,$$

and write $\mu(t),\beta(t)$ when $\alpha$ is fixed.

**Transition law.** For $x_0\ge0$ and $t>0$ the law of $X(t)$ given $X(0)=x_0$ is the Poisson-gamma mixture

$$f(x_0,x;t)=\delta(x)e^{-x_0\mu(t)}+\sum_{l\ge1}\frac{(x_0\mu(t))^l}{l!}e^{-x_0\mu(t)}\,\frac{x^{l-1}e^{-x/\beta(t)}}{\beta(t)^l(l-1)!},\qquad x\ge0.$$

**Genealogical reading.** The Feller diffusion is the limit of a linear birth-death process with birth and death rates $\tfrac12\epsilon^{-1}\pm\tfrac12\alpha+O(\epsilon)$ and population scaled by $\epsilon$, and of a near-critical Galton-Watson process. In these limits, the number $A_\infty(t)$ of time-$0$ ancestors of the population $X(t)$ is $\operatorname{Poisson}(x_0\mu(t))$, each ancestor's family has an independent exponential size with mean $\beta(t)$, and the population is extinct by time $t$ with probability $e^{-x_0\mu(t)}$. Jointly,

$$\mathbb P\bigl(A_\infty(t)=l,\ X(t)\in(x,x+dx)\mid X(0)=x_0\bigr)=\frac{(x_0\mu(t))^l}{l!}e^{-x_0\mu(t)}\frac{x^{l-1}e^{-x/\beta(t)}}{\beta(t)^l(l-1)!}\,dx,\qquad l\ge1.$$

**Sampling.** Conditional on $A_\infty(s)=l$ ancestors of the whole population at time $t-s$, a sample of size $n$ taken at time $t$ has $k\le l$ ancestors at time $t-s$ with probability

$$\mathbb P(A_n(s)=k\mid A_\infty(s)=l)=\binom lk\frac{n!}{l_{(n)}}\binom{n-1}{k-1},$$

independent of $X(0)$ and $X(t)$, where $l_{(n)}=l(l+1)\cdots(l+n-1)$.

## Proof idea

Solving the forward equation by a Laplace transform in $x$ gives $\mathbb E[e^{-\theta X(t)}\mid X(0)=x_0]=\exp\{-x_0\mu(t)\,\theta\beta(t)/(1+\theta\beta(t))\}$, the transform of a compound Poisson sum of exponentials, which is the mixture above. The sampling formula is a general property of exchangeable binary trees, applied to the Feller genealogy.

## Sources

- C. J. Burden and R. C. Griffiths, "The Feller diffusion conditioned on a single ancestral founder", Theoretical Population Biology 166 (2025), 1–15, <https://doi.org/10.1016/j.tpb.2025.09.001>. Numbering as in the preprint arXiv:2504.19428v3, <https://arxiv.org/abs/2504.19428v3>: Section 2 (the generator, the Poisson-gamma solution with $f_l$, $\mu$ and $\beta$, the diffusion limits of birth-death and Galton-Watson processes, and the subsection on numbers of ancestors and coalescent times) and Lemma 1.
