# Pólya–Aeppli law of ancestor numbers in a Feller diffusion

**Model.** The Feller diffusion with parameter $\alpha \in \mathbb{R}$ is the continuous-state branching process on $[0,\infty)$ with generator

$$\mathcal{L} = \tfrac12 x \frac{\partial^2}{\partial x^2} + \alpha x \frac{\partial}{\partial x},$$

started from $X(0) = x_0 > 0$; it is subcritical, critical or supercritical as $\alpha <0$, $=0$, $>0$, and arises as the scaling limit of birth–death and Bienaymé–Galton–Watson processes. Put

$$\mu(t;\alpha) = \frac{2\alpha e^{\alpha t}}{e^{\alpha t}-1}, \qquad \mu(t;0) = 2/t .$$

For $0 < s \le t$ let $A_\infty(s;t)$ be the (a.s. finite) number of ancestors, at time $t-s$, of the whole population alive at time $t$, and let $A_n(s;t)$ be the number of ancestors at time $t-s$ of a sample of $n$ individuals taken from the population at time $t$.

A random variable $Q = \sum_{i=0}^{N} M_i$ ($M_0 := 0$) with $N \sim \mathrm{Poisson}(\nu)$ independent of i.i.d. shifted geometric $M_i$, $\mathbb{P}(M = m) = (1-p)p^{m-1}$ for $m \ge 1$, is called **Pólya–Aeppli** (geometric compound Poisson) with parameters $(\nu, p)$.

**Theorem.** For every $\alpha$ and $x_0 > 0$:

1. $A_\infty(s;t)$ is Pólya–Aeppli with parameters

    $$\nu = x_0\,\mu(t;\alpha) = \frac{2\alpha x_0 e^{\alpha t}}{e^{\alpha t}-1}, \qquad p = p(s,t;\alpha) = \frac{e^{\alpha s} - e^{\alpha t}}{1 - e^{\alpha t}} \qquad (\alpha \ne 0),$$

    and, as the continuous limits at $\alpha = 0$, $\nu = 2x_0/t$ and $p = 1 - s/t$.

    In particular ($s = t$, $p = 0$) the number of founders at time $0$ of the time-$t$ population is $\mathrm{Poisson}(x_0\mu(t;\alpha))$.

2. Consequently, for $j = 1,\dots,n$, the number of ancestors at time $t-s$ of a sample of $n$ is

    $$\mathbb{P}(A_n(s;t) = j) = n!\binom{n-1}{j-1}\sum_{k \ge j}\binom{k}{j}\frac{1}{k_{(n)}}\,\mathbb{P}\big(A_\infty(s;t) = k \,\big|\, A_\infty(s;t) > 0\big),$$

    with rising factorial $k_{(n)} = k(k+1)\cdots(k+n-1)$.

## Expansion

The Feller transition law is Poisson–gamma: the time-$t$ population is a Poisson number of independent exponential families, one per founder. Applying this at times $t-s$ and $t$ (Markov property), each of the Poisson many founder families alive at time $t$ is split by its own descendants at time $t-s$ into a geometric number of subfamilies with non-empty progeny at $t$, giving the compound-Poisson-geometric structure. Given $k$ ancestral families, their relative sizes at time $t$ are Dirichlet$(1,\dots,1)$, i.e. uniform on the simplex, and sampling $n$ individuals from Dirichlet weights is a Pólya-urn computation: the sample has $j$ ancestors with probability $\binom{k}{j}\frac{n!}{k_{(n)}}\binom{n-1}{j-1}$, independent of the total mass. Averaging this over the law of $A_\infty$ from part 1 gives part 2.

## Sources

- Conrad J. Burden and Robert C. Griffiths, "Coalescence and sampling distributions for Feller diffusions", *Theoretical Population Biology* 155 (2024), 67–76, <https://doi.org/10.1016/j.tpb.2023.12.001>. Numbering as in the preprint arXiv:2210.12894v2, <https://arxiv.org/abs/2210.12894v2>: Definition 1, Theorem 1, Lemma 1 and Theorem 2.
