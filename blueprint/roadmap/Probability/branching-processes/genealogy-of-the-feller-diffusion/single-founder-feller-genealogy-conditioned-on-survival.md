# Single-founder Feller genealogy conditioned on survival

The Feller diffusion with parameter $\alpha\in\mathbb R$ has generator

$$\mathcal L=\tfrac12x\frac{\partial^2}{\partial x^2}+\alpha x\frac{\partial}{\partial x},$$

equivalently $dX=\sqrt{X}\,dW+\alpha X\,dt$; it is subcritical, critical or supercritical as $\alpha<0$, $=0$ or $>0$. Set

$$\mu(t;\alpha)=\frac{2\alpha e^{\alpha t}}{e^{\alpha t}-1},\qquad\beta(t;\alpha)=\frac{e^{\alpha t}-1}{2\alpha}\quad(\alpha\ne0),\qquad\mu(t;0)=\frac2t,\ \beta(t;0)=\frac t2,$$

and write $\mu(t),\beta(t)$ when $\alpha$ is fixed.

Consider a Feller diffusion on $[0,t]$ whose population at time $t$ descends from a single founder at time $0$ (the event $T_1=t$) and has not gone extinct. For $s\in[0,t]$ let $A_\infty(s)$ be the number of ancestors at time $t-s$ of the whole population $X(t)$, $A_n(s)$ that of an i.i.d. sample of size $n$, and $T_k$ the time back to the $k$-to-$(k-1)$ ancestor coalescence of the population.

**Theorem.**

1. The final population is exponential: $f_{X(t)\mid T_1=t}(x)=\beta(t)^{-1}e^{-x/\beta(t)}$, $x>0$.
2. The number of ancestors is geometric:

$$\mathbb P(A_\infty(s)=k\mid T_1=t,X(t)>0)=\frac{\beta(s)}{\beta(t)}\Bigl(1-\frac{\beta(s)}{\beta(t)}\Bigr)^{k-1},\qquad k\ge1.$$

3. The $k$-th coalescent time has density

$$f_{T_k\mid T_1=t,X(t)>0}(s)=\tfrac12(k-1)\frac{\mu(s)\beta(s)}{\beta(t)}\Bigl(1-\frac{\beta(s)}{\beta(t)}\Bigr)^{k-2},\qquad k\ge2.$$

4. For a sample of size $n$,

$$\mathbb P(A_n(s)=k\mid T_1=t)=\sum_{l\ge k}\binom lk\frac{n!}{l_{(n)}}\binom{n-1}{k-1}\frac{\beta(s)}{\beta(t)}\Bigl(1-\frac{\beta(s)}{\beta(t)}\Bigr)^{l-1},$$

and the time $T_2^{(n)}$ to the sample's most recent common ancestor satisfies

$$\mathbb P(T_2^{(n)}<s\mid T_1=t)=\frac{\beta(s)}{\beta(t)}\,{}_2F_1\Bigl(2,1;n+1;1-\frac{\beta(s)}{\beta(t)}\Bigr),\qquad0\le s\le t.$$

## Depends on

- [Poisson-gamma transition law of the Feller diffusion](poisson-gamma-transition-law-of-the-feller-diffusion.md)
- [Single-founder Feller genealogy conditioned on the current population size](single-founder-feller-genealogy-conditioned-on-the-current-population-size.md)

## Proof idea

The unconditioned statements are obtained by averaging the laws in [single-founder Feller genealogy conditioned on the current population size](single-founder-feller-genealogy-conditioned-on-the-current-population-size.md) over the exponential law of $X(t)$ in item 1. In the critical and supercritical cases this is a one-line computation: mixing $1+\operatorname{Poisson}(x\eta)$ with $\eta=1/\beta(s)-1/\beta(t)$ over $x\sim\operatorname{Exp}$ with mean $\beta(t)$ gives success probability $\beta(s)/\beta(t)$ for the geometric law. The sample formulas follow by mixing the exchangeable-tree sampling probabilities over this geometric law; the hypergeometric function collects the resulting series.

## Sources

- C. J. Burden and R. C. Griffiths, "The Feller diffusion conditioned on a single ancestral founder", Theoretical Population Biology 166 (2025), 1–15, <https://doi.org/10.1016/j.tpb.2025.09.001>. Numbering as in the preprint arXiv:2504.19428v3, <https://arxiv.org/abs/2504.19428v3>: Lemma 2, Theorem 2 and Theorem 4.
