# Single-founder Feller genealogy conditioned on the current population size

The Feller diffusion with parameter $\alpha\in\mathbb R$ has generator

$$\mathcal L=\tfrac12x\frac{\partial^2}{\partial x^2}+\alpha x\frac{\partial}{\partial x},$$

equivalently $dX=\sqrt{X}\,dW+\alpha X\,dt$; it is subcritical, critical or supercritical as $\alpha<0$, $=0$ or $>0$. Set

$$\mu(t;\alpha)=\frac{2\alpha e^{\alpha t}}{e^{\alpha t}-1},\qquad\beta(t;\alpha)=\frac{e^{\alpha t}-1}{2\alpha}\quad(\alpha\ne0),\qquad\mu(t;0)=\frac2t,\ \beta(t;0)=\frac t2,$$

and write $\mu(t),\beta(t)$ when $\alpha$ is fixed.

Consider a Feller diffusion on $[0,t]$ descended from a single founder at time $0$ (event $T_1=t$) and conditioned on the current population size $X(t)=x>0$. Let $A_\infty(s)$ be the number of ancestors of $X(t)$ at time $t-s$ and $T_k$ the population's $k$-th coalescent time. Write $\beta_s=\beta(s;|\alpha|)$, $\mu_s=\mu(s;|\alpha|)$, and $\eta(s,t)=1/\beta_s-1/\beta_t$.

**Theorem.**

1. The ancestor count is a shifted Poisson variable: for $k\ge1$,

$$\mathbb P(A_\infty(s)=k\mid T_1=t,X(t)=x)=\frac{(x\,\eta(s,t))^{k-1}}{(k-1)!}e^{-x\,\eta(s,t)}.$$

2. The coalescent times have marginal densities, for $t>s>0$ and $k\ge2$,

$$f_{T_k\mid T_1=t,X(t)=x}(s)=\frac{(x\,\eta(s,t))^{k-2}}{(k-2)!}\,\frac{x\mu_s}{2\beta_s}\,e^{-x\,\eta(s,t)}.$$

3. For an i.i.d. sample of size $n$, with $n_{[k]}$ and $n_{(k)}$ the falling and rising factorials and ${}_1F_1$ Kummer's function,

$$\mathbb P(A_n(s)=k\mid T_1=t,X(t)=x)=\frac{n_{[k]}}{n_{(k)}(k-1)!}(x\,\eta(s,t))^{k-1}e^{-x\,\eta(s,t)}\,{}_1F_1(k+1,k+n,x\,\eta(s,t)),\qquad1\le k\le n.$$

4. Letting the founder recede ($t\to\infty$), $A_\infty(s)$ converges weakly to $1+\operatorname{Poisson}(x/\beta_s)$, and the analogous limit holds for the sample count with $\eta(s,t)$ replaced by $1/\beta_s$. Under an improper uniform prior on $T_1$ instead, the posterior of $A_\infty(s)$ given $X(T_1)=x$ is exactly $\operatorname{Poisson}(x/\beta_s)$.

Since $\beta(\cdot;|\alpha|)$ appears, the genealogy given the current size depends on $\alpha$ only through $|\alpha|$: sub- and supercritical diffusions with the same $|\alpha|$ have the same conditioned genealogy.

## Depends on

- [Poisson-gamma transition law of the Feller diffusion](poisson-gamma-transition-law-of-the-feller-diffusion.md)

## Proof idea

Split $[0,t]$ at time $t-s$. By the Poisson-gamma transition law, the $k$ ancestors at time $t-s$ of $X(t)=x$ form a Poisson family structure whose sizes are i.i.d. exponential, and conditioning on a single founder at time $0$ weights the intermediate population by its own one-family probability. Combining the two exponentials gives a gamma-Poisson posterior in which only the difference $1/\beta_s-1/\beta_t$ survives, which yields the shifted Poisson law; the coalescent time densities follow by differentiating $\mathbb P(A_\infty(s)<k)$ in $s$.

## Sources

- C. J. Burden and R. C. Griffiths, "The Feller diffusion conditioned on a single ancestral founder", Theoretical Population Biology 166 (2025), 1–15, <https://doi.org/10.1016/j.tpb.2025.09.001>. Numbering as in the preprint arXiv:2504.19428v3, <https://arxiv.org/abs/2504.19428v3>: Lemma 3, Theorem 1, Theorem 3, Lemma 4, Theorem 6 and Theorem 7.
