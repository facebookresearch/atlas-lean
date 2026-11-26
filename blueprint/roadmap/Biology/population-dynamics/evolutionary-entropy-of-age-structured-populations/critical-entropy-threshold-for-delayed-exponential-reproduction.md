# Critical entropy threshold for delayed exponential reproduction

**Setting.** Consider the exponential–geometric family of reproductive densities with maturity age $A>0$ and decay rate $\beta>0$:
$$p_{A,\beta}(a)=\begin{cases}0,&a<A,\\ \beta e^{-\beta(a-A)},&a\ge A,\end{cases}$$
with one-year reference duration. Then the cycle entropy is $S(A,\beta)=1-\log\beta$, the generation time is $T(A,\beta)=A+1/\beta$, and the evolutionary entropy is
$$H(A,\beta)=\frac{S}{T}=\frac{\beta(1-\log\beta)}{1+A\beta}.$$

**Theorem 8 (continuous critical threshold).** For every $A>0$, $\beta\mapsto H(A,\beta)$ has a unique global maximum on $(0,\infty)$, attained at
$$\beta_c(A)=\frac{W(A)}{A},$$
where $W$ is the principal Lambert $W$-function. The critical point equation is $\log\beta+A\beta=0$, i.e. $\beta=e^{-A\beta}$.

**Theorem 7 (exact discrete transport).** On a mesh of step $h$ the geometric weights $q_h=e^{-\beta h}$ reproduce $S$, $T$ and $H$ exactly when within-class information is retained.

**Theorems 9–10 (corrected discrete threshold).** For $A>0$, $h>0$ the corrected discrete entropy rate $\dfrac{S_h(q)+\log h}{A+hq/(1-q)}$ has a unique maximum on $0<q<1$ at the root of $1-q=h\,q^{A/h}$. Writing $q=e^{-\beta h}$, the maximizing rate satisfies
$$\beta^{\rm disc}_{c,h}=\beta_c+\frac{\beta_c^2}{2(1+A\beta_c)}\,h+O(h^2)\xrightarrow[h\to0]{}\beta_c(A).$$

## Depends on

- [Entropy–potential decomposition and temporal invariance of evolutionary entropy](entropy-potential-decomposition-and-temporal-invariance-of-evolutionary-entropy.md)

## Expansion

Differentiating, $\partial_\beta H(A,\beta)=-\dfrac{\log\beta+A\beta}{(1+A\beta)^2}$; the numerator $\log\beta+A\beta$ is strictly increasing from $-\infty$ to $+\infty$, so $H$ increases then decreases and the maximum is unique. Writing $A\beta=x$, the equation $xe^{x}=A$ gives $x=W(A)$. At the maximum $1-\log\beta_c=1+A\beta_c$, so $H_{\max}(A)=\beta_c(A)$. Delayed maturity therefore caps evolutionary entropy: species with large $A$ have small $\beta_c$, that is slow post-maturity decay of reproduction and long reproductive lifespans, the regime invoked to explain extreme longevity.

## Sources

- J. Buescu, H. M. Oliveira, "Temporal invariance of evolutionary entropy and comparative demographic analysis", arXiv preprint (2026), Theorems 7–10, <https://doi.org/10.48550/arXiv.2610.15466>.
