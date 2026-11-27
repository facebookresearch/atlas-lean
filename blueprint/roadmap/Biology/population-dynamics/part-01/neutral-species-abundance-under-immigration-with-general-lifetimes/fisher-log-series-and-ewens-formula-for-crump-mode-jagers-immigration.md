# Fisher's log-series and Ewens' formula for neutral communities with immigration and general lifetimes

**Model.** Individuals have i.i.d. lifetimes with an arbitrary law $\Lambda/\lambda$ on $(0,\infty]$ (lifetime measure $\Lambda$ of mass $\lambda$) and, while alive, give birth at constant rate $\lambda$; offspring inherit the parent's species. The descendance of one individual is a homogeneous binary Crump–Mode–Jagers process (a splitting tree), generally not Markov. Starting from an empty island, immigrants of entirely new species arrive at the times of a Poisson process of rate $\mu$. Let $\psi(a)=a-\int_{(0,\infty]}(1-e^{-ar})\,\Lambda(dr)$ and let $W$ be the scale function, the non-decreasing function with $W(0)=1$ and $\int_0^\infty e^{-ax}W(x)\,dx=1/\psi(a)$ for $a$ large; given that it is not extinct, the size at time $t$ of a population founded by one newborn individual at time $0$ is geometric with success probability $1/W(t)$. Let $I_t(k)$ be the number of species represented by exactly $k$ individuals at time $t$ ($I_t(0)$: immigrant families with no living descendant) and $\gamma=\mu/\lambda$.

**Theorem.** For every $t>0$ the variables $I_t(0),I_t(1),I_t(2),\dots$ are independent Poisson random variables with

$$\mathbb E\,I_t(k)=\frac{\gamma}{k}\Bigl(1-\frac1{W(t)}\Bigr)^k\quad(k\ge1),\qquad \mathbb E\,I_t(0)=\mu t-\gamma\ln W(t).$$

Thus the abundance distribution at any time is Fisher's log-series with parameter $\alpha_t=1-1/W(t)$.

**Corollary (Ewens' sampling formula).** Let $Y_1,Y_2,\dots$ be independent with $Y_k\sim\mathrm{Poisson}(\gamma/k)$. Conditional on the total population size $I_t=\sum_kkI_t(k)=n$, the vector $(I_t(1),\dots,I_t(n))$ has the law of $(Y_1,\dots,Y_n)$ conditioned on $\sum_{k=1}^nkY_k=n$, i.e. the Ewens sampling formula with parameter $\gamma$; this law depends neither on $t$ nor on the lifetime distribution. In particular, as $n\to\infty$, $I_n(k)$ converges in law to a Poisson variable with mean $\gamma/k$.

## Depends on

- [Ewens sampling formula and the Chinese restaurant process](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/README.md)

## Expansion

The number of immigrants by time $t$ is $\mathrm{Poisson}(\mu t)$ and, given their number, their arrival times are i.i.d. uniform on $[0,t]$; their families evolve independently. Hence the family sizes form a Poisson-randomized multinomial sample, which makes the counts $I_t(k)$ independent Poisson with means $\mu t\,P(Z_t=k)$, where $Z_t$ is the size at time $t$ of a family founded at a uniform time in $[0,t]$. The key computation, via the representation of a splitting tree's population size through its Lévy-process contour (geometric conditional sizes with parameter $1/W(s)$), gives

$$P(Z_t=k)=\frac1{\lambda kt}\Bigl(1-\frac1{W(t)}\Bigr)^k\ (k\ge1),\qquad P(Z_t=0)=1-\frac{\ln W(t)}{\lambda t},$$

using $\frac{d}{ds}\ln W(s)$ to integrate the geometric weights over $s\in[0,t]$. Finally, for independent Poisson counts with means $c\,\alpha^k/k$, conditioning on $\sum_kkX_k=n$ eliminates $\alpha$ (the conditional law is proportional to $\prod_k(c/k)^{x_k}/x_k!$), which yields Ewens' formula and the cancellation of $t$.

## Sources

- Amaury Lambert, "Species abundance distributions in neutral models with immigration or mutation and general lifetimes", arXiv (2010); Journal of Mathematical Biology 63 (2011). Section 3 (Lemma 3.1, scale function), Section 4 (Theorem 4.1, Corollary 4.2, Proposition 4.3, Lemma 4.4). <https://doi.org/10.48550/arXiv.1009.0118>. Published version: Journal of Mathematical Biology 63(1) (2011), 57–72, <https://doi.org/10.1007/s00285-010-0361-9>; locators above refer to the arXiv version.
